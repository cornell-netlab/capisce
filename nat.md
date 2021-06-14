# Real-World Example

We're going to look at a [simple NAT
program](https://github.com/p4lang/p4c/blob/main/testdata/p4_14_samples/simple_nat.p4).
I'm pretty sure this is the simple_nat example from the [bf4
paper](http://nets.cs.pub.ro/~costin/files/bf4.pdf). It seems like the authors
used the p4c test suite as their test dataset,

The table in the bf4 paper reports 7 total bugs, with 2 available after "infer", and all of them are fixed by "Fixes".

I'm still not sure what these bugs are, because theyre not reported in the paper
or in supplementary material.

I think 

## The Program

The program, as its name suggests, is a simple Network Address Translation (NAT)
program. I.e. it maps one TCP/IP address space to another.

### Headers

The program runs on a simple set of headers: ETH, IP, and TCP, with optional CPU encapsulation.
It also has intrinsic metadata and a custom metadata instance `meta`, both of which are defined below:

```
header_type intrinsic_metadata_t {
    fields {
        mcast_grp : 4;
        egress_rid : 4;
    }
}

metadata intrinsic_metadata_t intrinsic_metadata;

header_type meta_t {
    fields {
        do_forward : 1;
        ipv4_sa : 32;
        ipv4_da : 32;
        tcp_sp : 16;
        tcp_dp : 16;
        nhop_ipv4 : 32;
        if_ipv4_addr : 32;
        if_mac_addr : 48;
        is_ext_if : 1;
        tcpLength : 16;
        if_index : 8;
    }
}

metadata meta_t meta;
```

### Parser

The parser is pretty standard. The important thing we need to model is that some values are copied.

```
parser start {
    set_metadata(meta.if_index, standard_metadata.ingress_port);
    return select(current(0, 64)) {
        0 : parse_cpu_header;  // dummy transition
        default: parse_ethernet;
    }
}

parser parse_cpu_header {
    extract(cpu_header);
    set_metadata(meta.if_index, cpu_header.if_index);
    return parse_ethernet;
}

parser parse_ethernet {
    extract(ethernet);
    return select(latest.etherType) {
        ETHERTYPE_IPV4 : parse_ipv4;
        default: ingress;
    }
}

parser parse_ipv4 {
    extract(ipv4);
    set_metadata(meta.ipv4_sa, ipv4.srcAddr);
    set_metadata(meta.ipv4_da, ipv4.dstAddr);
    set_metadata(meta.tcpLength, ipv4.totalLen - 20);
    return select(ipv4.protocol) {
        IP_PROT_TCP : parse_tcp;
        default : ingress;
    }
}
parser parse_tcp {
    extract(tcp);
    set_metadata(meta.tcp_sp, tcp.srcPort);
    set_metadata(meta.tcp_dp, tcp.dstPort);
    return ingress;
}
```

### Tables 

There are 6 tables in this program, whose purposes are described at a high level
in the following, well, table:

| Table Name    | stage   | Purpose                                                                         |
|:-------------:|:--------|:--------------------------------------------------------------------------------|
| `if_info`     | ingress | read `meta_if_index` and drop or update IF info fields in `meta`                |
| `nat`         | ingress | Update metdata fields to perform NAT                                            |
| `ipv4_lpm`    | ingress | LPM `meta.ipv4_da` and drop or set `nhop_ipv4`, `egress_spec` and decrement TTL |
| `forward`     | ingress | update destination MAC based on `nhop_ipv4` (or drop)                           |
| `send_frame`  | egress  | copy metadata fields saved NAT into header values                               |
| `send_to_cpu` | egress  | always encapsulates the packet in a CPU header.                                 |


### Control Flow.

The control blocks are as follows. Between the Ingress and the Egress blocks, on
bmv2, the packet is dropped based on the value of
`standard_metadata.egress_spec`.

#### Ingress
```
apply(if_info);
apply(nat);
if(meta.do_forward == 1 && ipv4.ttl > 0){
  apply(ipv4_lpm);
  apply(forward);
}
```

### Egress

```
apply(standard_metadata.instance_type ==  0){
  apply(send_frame);
} else {
  apply(send_to_cpu);
}
```

### Encoding

First we (manually) encode the parser:

```
// nothing starts valid
cpu_header.isValid := 0;
ethernet.isValid := 0;
ipv4.isValid := 0;
tcp.isValid := 0;

// Start parsing
meta.if_index := standard_metadata.ingress_port;
{ assume pkt.lookahead == 0;
  cpu_header.isValid := 1;
  cpu_header.preamble := pkt.lookahead;
  meta.if_index := cpu_header.if_index;
  ethernet.isValid := 1;
} [] {
  assume pkt.lookahead != 0;
  ethernet.isValid := 1;
  ethernet.dstAddr := pkt.lookahead[0:48];
  ethernet.srcAddr := pkt.lookahead[0:16] @ ethernet.srcAddr[16:48];
};
{ assume ethernet.etherType == ETHERTYPE_IPV4;
  ipv4.isValid := 1;
  meta.ipv4_sa := ipv4.srcAddr;
  meta.ipv4_da := ipv4.dstAddr;
  meta.tcpLength := ipv4.totalLen - 20;
  { assume ipv4.protocol == IP_PROT_TCP;
    tcp.isValid := 1;
    meta.tcp_sp := tcp.srcPort;
    meta.tcp_dp := tcp.dstPort;
  } [] {
    assume ipv4.protocol != IP_PROT_TCP;
  }
} [] { 
  assume ethernet.etherType != ETHERTYPE_IPV4;
}
```

And then we use the algorithm written up in [inference.pdf](./inference.pdf).

```
// if_info
assume γ_if_info.meta.if_index = meta.if_index;
{ // hit
  assume ρ_if_info.key.meta.if_index == meta.if_index; // match condition
  assume γ_if_info.miss == 0;
  assume γ_if_info.hitAction == _ρ_if_info.id;
  { // _drop
    assume ρ_if_info.action == 0;
    standard_metadata.egress_spec == DROP;
  } [] { 
    // set_if_info
    assume ρ_if_info.action == 1; 
    meta.if_ipv4_addr := ρ_if_info.data.ipv4_addr;
    meta.if_mac_addr := ρ_if_info.data.mac_addr;
     meta.if_ext_if := ρ_if_info.data.is_ext;
  }
} [] { // miss
  assume ghost_if_info.miss == 1
};

// nat
assume γ_nat.meta.is_ext_if = meta.is_ext_if; 
assume γ_nat.meta.ipv4.isValid = ipv4.isValid;
assume γ_nat.meta.tcp.isValid = tcp.isValid;
assume γ_nat.ipv4.srcAddr = ipv4.srcAddr;
assume γ_nat.ipv4.dstAddr = ipv4.dstAddr;
assume γ_nat.tcp.srcPort = tcp.srcPort;
assume γ_nat.tcp.dstPort = tcp.dstPort;
{ // hit
  assume meta.is_ext_if = ρ_nat.meta.is_ext_if;
  assume ipv4.isValid = ρ_nat.ipv4.isValid;
  assume tcp.isValid = ρ_nat.tcp.isValid;
  assume ipv4.srcAddr & ρ_nat.ipv4.srcAddrMask = ρ_nat.ipv4.srcAddr & ρ_nat.ipv4.srcAddrMask;
  assume ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask = ρ_nat.ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask;
  assume tcp.srcPort & ρ_nat.tcp.srcPortMask = ρ_nat.tcp.srcPort & ρ_nat.tcp.srcPortMask
  assume tcp.dstPort & ρ_nat.tcp.dstPortMask = ρ_nat.tcp.dstPort & ρ_nat.tcp.dstPortMask;
 
  assume γ_nat.miss == 0;
  assume γ_nat.hitAction == ρ_nat.id;
  { // _drop
    assume ρ_nat.action == 0;
    standard_metadata.egress_spec == DROP;
  } [] { 
    // nat_miss_int_to_ext
    assume ρ_nat.action == 1;
    // clone_ingress_pkt_to_egress(CPU_MIRROR_SESSION_ID, copy_to_cpu_fields);
    standard_metadata.instance_type := CLONE; // CLONE != 0
  } [] {
    // nat_miss_ext_to_int
    assume ρ_nat.action == 2;
    meta.do_forward := 0;
    standard_metadata.egress_spec := DROP;
  } [] {
    // nat_hit_int_to_ext
    assume ρ_nat.action = 3;
    meta.do_forward := 1;
    meta.ipv4_sa := ρ_nat.data.srcAddr;
    meta.tcp_sp := ρ_nat.data.srcPort;
  } [] {
    // nat_hit_ext_to_int
    assume ρ_nat.action = 4;
    meta.do_forward := 1;
    meta.ipv4_da := ρ_nat.data.dstAddr;
    meta.tcp_da := ρ_nat.data.dstPort;
  } [] {
    // nat_no_nat
    assume ρ_nat.action = 5;
    meta.do_forward := 1;
  }
} [] { // miss
  assume γ_nat.miss == 1
};

{ // ipv4_lpm
  assume meta.do_forward == 1 ∧ ipv4.ttl > 0;
  assume γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da;
  { // hit
    assert 
    assume meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask = ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask; // TODO NEED ASSUMPTION ON MASK
    assume γ_ipv4_lpm.miss = 0;
    assume γ_ipv4_lpm.hitAction = ρ_ipv4_lpm.id;
    { // set_nhop
      ρ_ipv4_lpm.action = 0;
      meta.nhop_ipv4 := ρ_ipv4_lpm.nhop_ipv4;
      standard_metadata.egress_spec := ρ_ipv4_lpm.port;
      ipv4.ttl := ipv4.ttl - 1; 
    } [] { // _drop
      ρ_ipv4_lpm.action = 1;
      standard_metadata.egress_spec := DROP;
    }
  } [] { // miss
    γ_ipv4_lpm.miss = 1;
  };
  
  assume γ_forward.meta.nhop_ipv4 = meta.nhop_ipv4;
  { // hit
    assume meta.nhop_ipv4 = ρ_forward.nhop_ipv4;
    assume γ_forward.miss = 0;
    assume γ_forward.hitAction = ρ_forward.id;
    { // _set_dmac
      assume ρ_forward.action == 0;
      ethernet.dstAddr := ρ_forward.data.dmac;
    } [] { // _drop
      assume ρ_forward.action == 1;
      standard_metadata.egress_spec := DROP;
    }
  } [] { // miss
    assume γ_forward.miss = 1;
  } 
} [] {
  assume ¬(meta.do_forward == 1 ∧ ipv4.ttl > 0);
};

{ 
  assume standard_metadata.egress_spec == DROP 
} [] {
  assume standard_metadata.egress_spec != DROP;
  standard_metadata.egress_port := standard_metadata.egress_spec;
  { assume standard_metadata.instance_type == 0
    // send_frame
    assume standard_metdata.egress_port = γ_send_frame.standard_metadata.egress_port;
    { // hit
      assume standard_metadata.egress_port = ρ_send_frame.standard_metdata.egress_port;
      assume γ_send_frame.miss == 0;
      assume γ_forward.hitAction = ρ_send_frame.id;
      { // do_rewrites
        assume ρ_send_frame.action = 0;
        cpu_header.isValid := 0;
        ethernet.srcAddr := ρ_send_frame.smac;
        ipv4.srcAddr := meta.ipv4_sa;
        ipv4.dstAddr := meta.ipv4_da;
        tcp.srcPort := meta.tcp_sp;
        tcp.dstPort := meta.tcp_dp;
      } [] { // _drop
        assume ρ_send_frame.action = 1;
        standard_metadata.egress_spec := DROP; 
      }
    } [] { // miss
      assume γ_send_frame.miss == 1;
    }
  } [] {
    assume standard_metadata.instance_type != 0;
    // send_to_cpu
    { // hit
      assume γ_send_frame.miss == 0;
      assume γ_forward.hitAction == ρ_send_frame.id;
      // do_cpu_encap
      assume ρ_send_frame.action = 0;
      cpu_header.isValid := 1;
      cpu_header.preamble := 0;
      cpu_header.device := 0;
      cpu_header.device := 0xab;
      cpu_header.if_index := meta.if_index;
    } [] {
      // miss
      assume γ_send_frame.miss == 1
    }
  }
}
```


### The program, assert-specified to avoid Uninitialized Reads

We annotate the above program to ensure that there are no reads of uninitialized values.

We track whether a field `x.f` has been initialized using the suffix `.init`.
E.g. for `meta.if_index` we introduce the `1`-bit ghost variable
`meta.if_index.init`.

```
// nothing starts valid
cpu_header.isValid := 0;
ethernet.isValid := 0;
ipv4.isValid := 0;
tcp.isValid := 0;

// Nothing is initalized except standard/intrinsic metadata, and pkt.lookahead:
....

// Start parsing
meta.if_index := standard_metadata.ingress_port;
{ assume pkt.lookahead == 0;
  cpu_header.isValid := 1;
  cpu_header.preamble.init := 1;
  cpu_header.device.init := 1;
  cpu_header.reason.init := 1;
  cpu_header.if_index.init := 1;
  cpu_header.preamble := pkt.lookahead;
  assert cpu_header.if_index.init == 1;
  meta.if_index := cpu_header.if_index;
  ethernet.isValid := 1;
  ethernet.dstAddr.init := 1;
  ethernet.srcAddr.init := 1;
  ethernet.etherType.init:= 1;
} [] {
  assume pkt.lookahead != 0;
  ethernet.isValid := 1;
  ethernet.dstAddr.init := 1;
  ethernet.srcAddr.init := 1;
  ethernet.etherType.init:= 1;
  ethernet.dstAddr := pkt.lookahead[0:48];
  ethernet.srcAddr := pkt.lookahead[0:16] @ ethernet.srcAddr[16:48];
};
{ assume ethernet.etherType == ETHERTYPE_IPV4;
  ipv4.isValid := 1;
  ipv4.*.init := 1; // shorthand for enumerating all header fields.
  assert ipv4.srcAddr.init := 1;
  meta.ipv4_sa := ipv4.srcAddr;
  meta.ipv4_sa := 1;
  assert ipv4.dstAddr.init := 1;
  meta.ipv4_da := ipv4.dstAddr;
  meta.ipv4_da := 1;
  assert ipv4.totalLen := 1;
  meta.tcpLength := ipv4.totalLen - 20;
  meta.tcpLength.init := 1;
  { assume ipv4.protocol == IP_PROT_TCP;
    tcp.isValid := 1;
    tcp.*.init := 1;
    assert tcp.srcPort.init == 1;
    meta.tcp_sp := tcp.srcPort;
    meta.tcp_sp.init := 1;
    meta.tcp_dp := tcp.dstPort;
    meta.tcp_dp.init := 1;
  } [] {
    assume ipv4.protocol != IP_PROT_TCP;
  }
} [] { 
  assume ethernet.etherType != ETHERTYPE_IPV4;
}
```

Now we track to make sure there are no undefined reads. We also need to model the short-circuiting behavior of ternary and lpm reads.

```
// if_info
assert meta.if_index.init == 1;
assume γ_if_info.meta.if_index = meta.if_index;
{ // hit
  assume ρ_if_info.key.meta.if_index == meta.if_index; // match condition
  assume γ_if_info.miss == 0;
  assume γ_if_info.hitAction == ρ_if_info.id;
  { // _drop
    assume ρ_if_info.action == 0;
    standard_metadata.egress_spec == DROP;
  } [] { 
    // set_if_info
    assume ρ_if_info.action == 1; 
    meta.if_ipv4_addr := ρ_if_info.data.ipv4_addr;
    meta.if_mac_addr := ρ_if_info.data.mac_addr;
    meta.if_ext_if := ρ_if_info.data.is_ext;
  }
} [] { // miss
  assume ghost_if_info.miss == 1
};

// nat
assume γ_nat.meta.is_ext_if = meta.is_ext_if; 
assume γ_nat.meta.ipv4.isValid = ipv4.isValid;
assume γ_nat.meta.tcp.isValid = tcp.isValid;
assume γ_nat.ipv4.srcAddr = ipv4.srcAddr;
assume γ_nat.ipv4.dstAddr = ipv4.dstAddr;
assume γ_nat.tcp.srcPort = tcp.srcPort;
assume γ_nat.tcp.dstPort = tcp.dstPort;

assert meta.is_ext_if.init == 1;
{ // hit
  assume meta.is_ext_if = ρ_nat.meta.is_ext_if;
  assume ipv4.isValid = ρ_nat.ipv4.isValid;
  assume tcp.isValid = ρ_nat.tcp.isValid;
  { assume ρ_nat.ipv4.srcAddrMask == 0 }
  [] {
    assume ρ_nat.ipv4.srcAddrMask != 0;
    assert ipv4.srcAddr.init == 1;
    assume ipv4.srcAddr & ρ_nat.ipv4.srcAddrMask = ρ_nat.ipv4.srcAddr & ρ_nat.ipv4.srcAddrMask
  };
  { assume ρ_nat.ipv4.dstAddrMask == 0 }
  [] {
    assume ρ_nat.ipv4.dstAddrMask != 0;
    assert ipv4.dstAddr.init == 1;
    assume ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask = ρ_nat.ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask
  };
  { assume ρ_nat.tcp.srcPortMask = 0 }
  [] {
    assume ρ_nat.tcp.srcPortMask != 0
    assert tcp.srcPort.init = 1
    assume tcp.srcPort & ρ_nat.tcp.srcPortMask = ρ_nat.tcp.srcPort & ρ_nat.tcp.srcPortMask
  };
  { assume ρ_nat.tcp.dstPortMask = 0 }
  [] {
    assume ρ_nat.tcp.dstPortMask != 0
    assert tcp.dstPort.init = 1
    assume tcp.dstPort & ρ_nat.tcp.dstPortMask = ρ_nat.tcp.dstPort & ρ_nat.tcp.dstPortMask
  };
  assume γ_nat.miss == 0;
  assume γ_nat.hitAction == ρ_nat.id;
  { // _drop
    assume ρ_nat.action == 0;
    standard_metadata.egress_spec == DROP;
  } [] { 
    // nat_miss_int_to_ext
    assume ρ_nat.action == 1;
    // clone_ingress_pkt_to_egress(CPU_MIRROR_SESSION_ID, copy_to_cpu_fields);
    standard_metadata.instance_type := CLONE; // CLONE != 0
  } [] {
    // nat_miss_ext_to_int
    assume ρ_nat.action == 2;
    meta.do_forward := 0;
    standard_metadata.egress_spec := DROP;
  } [] {
    // nat_hit_int_to_ext
    assume ρ_nat.action = 3;
    meta.do_forward := 1;
    meta.ipv4_sa := ρ_nat.data.srcAddr;
    meta.tcp_sp := ρ_nat.data.srcPort;
  } [] {
    // nat_hit_ext_to_int
    assume ρ_nat.action = 4;
    meta.do_forward := 1;
    meta.ipv4_da := ρ_nat.data.dstAddr;
    meta.tcp_da := ρ_nat.data.dstPort;
  } [] {
    // nat_no_nat
    assume ρ_nat.action = 5;
    meta.do_forward := 1;
  }
} [] { // miss
  assume γ_nat.miss == 1
};

{ // ipv4_lpm
  assert meta.do_forward.init == 1;
  assume meta.do_forward == 1;
  assert ipv4.ttl.init == 1;
  assume ipv4.ttl > 0;
  assume γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da;
  { // hit
    { assume ρ_ipv4_lpm.ipv4_daMask == 0 }
    [] {
      assume ρ_ipv4_lpm.ipv4_daMask != 0;
      assert meta.ipv4_da.init == 1;
      assume meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask = ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask; // TODO NEED ASSUMPTION ON MASK
    };
    assume γ_ipv4_lpm.miss == 0;
    assume γ_ipv4_lpm.hitAction = ρ_ipv4_lpm.id;
    { // set_nhop
      assume ρ_ipv4_lpm.action == 0;
      meta.nhop_ipv4 := ρ_ipv4_lpm.nhop_ipv4;
      meta.nhop_ipv4.init := 1;
      standard_metadata.egress_spec := ρ_ipv4_lpm.port;
      assert ipv4.ttl.init == 1;
      ipv4.ttl := ipv4.ttl - 1; 
    } [] { // _drop
      assume ρ_ipv4_lpm.action == 1;
      standard_metadata.egress_spec := DROP;
    }
  } [] { // miss
    assume γ_ipv4_lpm.miss == 1;
  };
  
  assert meta.nhop_ipv4.init == 1;
  assume γ_forward.meta.nhop_ipv4 = meta.nhop_ipv4;
  { // hit
    assume meta.nhop_ipv4 == ρ_forward.nhop_ipv4;
    assume γ_forward.miss = 0;
    assume γ_forward.hitAction = ρ_forward.id;
    { // _set_dmac
      assume ρ_forward.action == 0;
      ethernet.dstAddr := ρ_forward.data.dmac;
    } [] { // _drop
      assume ρ_forward.action == 1;
      standard_metadata.egress_spec := DROP;
    }
  } [] { // miss
    assume γ_forward.miss = 1;
  } 
} [] {
  assume ¬(meta.do_forward == 1 ∧ ipv4.ttl > 0);
};

{ 
  assume standard_metadata.egress_spec == DROP 
} [] {
  assume standard_metadata.egress_spec != DROP;
  standard_metadata.egress_port := standard_metadata.egress_spec;
  { assume standard_metadata.instance_type == 0
    // send_frame
    assume standard_metdata.egress_port == γ_send_frame.standard_metadata.egress_port;
    { // hit
      assume standard_metadata.egress_port = ρ_send_frame.standard_metadata.egress_port;
      assume γ_send_frame.miss == 0;
      assume γ_forward.hitAction = ρ_send_frame.id;
      { // do_rewrites
        assume ρ_send_frame.action = 0;
        cpu_header.isValid := 0;
        cpu_header.preamble.init := 0;
        cpu_header.device.init := 0;
        cpu_header.reason.init := 0;
        cpu_header.if_index.init := 0;
        ethernet.srcAddr := ρ_send_frame.smac;
        
        assert meta.ipv4_sa.init == 1;
        ipv4.srcAddr := meta.ipv4_sa;
        {assume ipv4.isValid == 1; ipv4.srcAddr.init := 1} [] {assume ipv4.isValid == 0};
        
        assert meta.ipv4_da.init == 1;
        ipv4.dstAddr := meta.ipv4_da;
        {assume ipv4.isValid == 1; ipv4.dstAddr.init := 1} [] {assume ipv4.isValid == 0};
        
        assert meta.tcp_sp.init == 1;
        tcp.srcPort := meta.tcp_sp;
        {assume tcp.isValid == 1; tcp.srcPort.init := 1} [] {assume tcp.isValid == 0};
        
        assert meta.tcp_dp.init == 1;
        tcp.dstPort := meta.tcp_dp;
        {assume tcp.isValid == 1; tcp.dstPort.init := 1} [] {assume tcp.isValid == 0};
      
      } [] { // _drop
        assume ρ_send_frame.action == 1;
        standard_metadata.egress_spec := DROP; 
      }
    } [] { // miss
      assume γ_send_frame.miss == 1;
    }
  } [] {
    assume standard_metadata.instance_type != 0;
    // send_to_cpu
    { // hit
      assume γ_send_frame.miss == 0;
      assume γ_forward.hitAction == ρ_send_frame.id;
      // do_cpu_encap
      assume ρ_send_frame.action = 0;
      cpu_header.isValid := 1;
      cpu_header.preamble := 0;
      cpu_header.device := 0;
      cpu_header.device := 0xab;
      assert meta.if_index.init == 1;
      cpu_header.if_index := meta.if_index;
    } [] {
      // miss
      assume γ_send_frame.miss == 1
    }
  }
}
```




### Computing the Weakest Precondition



First Compute the weakest precondition of egress.

```
ϕₑ ≜
standard_metadata.egress_spec != DROP ⇒
( standard_metadata.instance_type == 0 ⇒
   (standard_metdata.egress_spec == γ_send_frame.standard_metadata.egress_port) ⇒
      ( (standard_metadata.egress_spec == ρ_send_frame.standard_metadata.egress_port
         ∧ γ_send_frame.miss == 0
         ∧ γ_forward.hitAction = ρ_send_frame.id
         ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                       ∧ meta.ipv4_da.init == 1 
                                       ∧ meta.tcp_sp.init == 1
                                       ∧ meta.tcp_dp.init == 1)))
  ∧
  standard_metadata.instance_type != 0 ⇒
    (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ assume ρ_send_frame.action = 0 ⇒
       (meta.if_index.init == 1))
```


Now push this formula through `forward` to get

```
meta.nhop_ipv4.init == 1 ∧
(γ_forward.meta.nhop_ipv4 == meta.nhop_ipv4 ⇒
  ((meta.nhop_ipv4 == ρ_forward.nhop_ipv4
    ∧ γ_forward.miss = 0
    ∧ γ_forward.hitAction = ρ_forward.id)
   ⇒ (ρ_forward.action == 0 ⇒ ϕₑ[ρ_forward.data.dmac / ethernet.dstAddr])
     ∧ (ρ_forward.action == 1 ⇒ ϕₑ[DROP / standard_metadata.egress_spec])
   )
  ∧
  (γ_forward.miss == 1 ⇒ ϕₑ))
```

Note that `ϕₑ[DROP / standard_metadata.egress_spec] = ⊤` and
`ϕₑ[ρ_forward.data.dmac / ethernet.dstAddr] = ϕₑ`. So we can simplify this to 

```
ϕ_f ≜
meta.nhop_ipv4.init == 1 ∧
(γ_forward.meta.nhop_ipv4 == meta.nhop_ipv4 ⇒
  ((meta.nhop_ipv4 == ρ_forward.nhop_ipv4
    ∧ γ_forward.miss == 0
    ∧ γ_forward.hitAction = ρ_forward.id)
   ⇒ (ρ_forward.action == 0 ⇒ ϕₑ)
   )
  ∧
  (γ_forward.miss == 1 ⇒ ϕₑ))
```


Now we push `ϕ_f` back through ipv4_lpm and get the following.

The miss case is
```
 γ_ipv4_lpm.miss == 1⇒ ϕ_f
```

The actions are 

```
(ρ_ipv4_lpm.action == 0 ⇒ 
     (ipv4.ttl.init == 1 ∧ 
         ϕ_f[ρ_ipv4_lpm.port / standard_metadata.egress_spec]
            [ρ_ipv4_lpm.nhop_ivp4 / meta.nhop_ivp4]
            [1 / meta.nhop_ipv4.init]))
∧  ρ_ipv4_lpm.action == 1 ⇒ ϕ_f[DROP/standard_metadata.egress_spec] 
```

We can write 
```
ϕ_f[ρ_ipv4_lpm.port / standard_metadata.egress_spec]
            [ρ_ipv4_lpm.nhop_ivp4 / meta.nhop_ivp4]
            [1 / meta.nhop_ipv4.init]
```
as the simplified 
```
ϕ₀ ≜
(γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ipv4 ⇒
  ((ρ_ipv4_lpm.nhop_ipv4 == ρ_forward.nhop_ipv4
    ∧ γ_forward.miss == 0
    ∧ γ_forward.hitAction = ρ_forward.id)
   ⇒ (ρ_forward.action == 0 ⇒ ϕₑ[ρ_ipv4_lpm.port/standard_specetadata.egress_spec])
   )
  ∧
  (γ_forward.miss == 1 ⇒ ϕₑ[ρ_ipv4_lpm.port/standard_specetadata.egress_spec]))
```

and `ϕ_f[DROP/standard_metadata.egress_spec]` as 


So the condition at the application of ipv4_lpm is

```
ϕ_ipv4_lpm ≜
γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
  ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
  ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
        meta.ipv4_da.init == 1
        ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
           ⇒ ϕ_ipv4_lpm_inner))

where
ϕ_ipv4_lpm_inner ≜
γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction = ρ_ipv4_lpm.id
⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
     (ipv4.ttl.init == 1 ∧ 
         ϕ_f[ρ_ipv4_lpm.port / standard_metadata.egress_spec]
            [ρ_ipv4_lpm.nhop_ivp4 / meta.nhop_ivp4]
            [1 / meta.nhop_ipv4.init]))
     ∧  ρ_ipv4_lpm.action == 1 ⇒ ϕ_f[DROP/standard_metadata.egress_spec] )
```

And the if-statement produces the following (no short-circuting, for simplicity):

```
ϕ_b ≜
 meta.do_forward.init == 1 ∧ ipv4.ttl.init == 1 ∧
 ( meta.do_forward == 1 ∧ ipv4.ttl > 0 ⇒ ϕ_ipv4_lpm
 ∧ ¬ (meta.do_forward == 1 ∧ ipv4.ttl > 0) ⇒ ϕₑ
```

## TODO :: SIMPLY PUSH ϕ_b through `nat` and `if_info`
