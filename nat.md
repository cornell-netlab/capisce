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
  assume ρ_if_info.meta.if_index == meta.if_index; // match condition
  assume γ_if_info.miss == 0;
  assume γ_if_info.hitAction == ρ_if_info.id;
  { // _drop
    assume ρ_if_info.action == 0;
    standard_metadata.egress_spec := DROP;
  } [] { 
    // set_if_info
    assume ρ_if_info.action == 1; 
    meta.if_ipv4_addr := ρ_if_info.data.ipv4_addr;
    meta.if_mac_addr := ρ_if_info.data.mac_addr;
    meta.is_ext_if := ρ_if_info.data.is_ext;
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
    meta.tcp_dp := ρ_nat.data.dstPort;
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
    assume standard_metadata.egress_port = γ_send_frame.standard_metadata.egress_port;
    { // hit
      assume standard_metadata.egress_port = ρ_send_frame.standard_metadata.egress_port;
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


The formulae that I expect to synthesize are:

```
ρ_nat.ipv4.isValid == 0 ⇒ (ρ_nat.ipv4.srcAddrMask == 0 ∧ ρ_nat.ipv4.dstAddrMask == 0)

ρ_nat.tcp.isValid == 0 ⇒ (ρ_nat.tcp.srcPortMask == 0 ∧ ρ_nat.tcp.dstPortMask == 0)

ρ_nat.ipv4.isValid == 0 ⇒ (ρ_nat.action ∈ {nat_miss_ext_to_int})

ρ_ipv4_lpm.hit == 0 ∧ ρ_ipv4_lpm.action == set_nhop



```


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
  meta.if_index.init := 1;
  ethernet.isValid := 1;
  ethernet.dstAddr.init := 1;
  ethernet.srcAddr.init := 1;
  ethernet.etherType.init := 1;
} [] {
  assume pkt.lookahead != 0;
  ethernet.isValid := 1;
  ethernet.dstAddr.init := 1;
  ethernet.srcAddr.init := 1;
  ethernet.etherType.init:= 1;
  assume ethernet.dstAddr == pkt.lookahead[0:48];
  assume ethernet.srcAddr[0:16] == ethernet.srcAddr[0:16]
};
{ assume ethernet.etherType == ETHERTYPE_IPV4;
  ipv4.isValid := 1;
  ipv4.*.init := 1; // shorthand for enumerating all header fields.
  assert ipv4.srcAddr.init == 1;
  meta.ipv4_sa := ipv4.srcAddr;
  meta.ipv4_sa := 1;
  assert ipv4.dstAddr.init == 1;
  meta.ipv4_da := ipv4.dstAddr;
  meta.ipv4_da.init := 1;
  assert ipv4.totalLen.init == 1;
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
  assume ρ_if_info.meta.if_index == meta.if_index; // match condition
  assume γ_if_info.miss == 0;
  assume γ_if_info.hitAction == ρ_if_info.id;
  { // _drop
    assume ρ_if_info.action == 0;
    standard_metadata.egress_spec == DROP;
  } [] { 
    // set_if_info
    assume ρ_if_info.action == 1; 
    meta.if_ipv4_addr := ρ_if_info.data.ipv4_addr;
    meta.if_ipv4_addr.init := 1
    meta.if_mac_addr := ρ_if_info.data.mac_addr;
    meta.if_mac_addr.init := 1;
    meta.is_ext_if := ρ_if_info.data.is_ext;
    meta.is_ext_if.init := 1;
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
    meta.ipv4_sa.init := 1;
    meta.tcp_sp := ρ_nat.data.srcPort;
    meta.tcp_sp.init := 1;
  } [] {
    // nat_hit_ext_to_int
    assume ρ_nat.action = 4;
    meta.do_forward := 1;
    meta.ipv4_da := ρ_nat.data.dstAddr;
    meta.ipv4_da.init := 1;
    meta.tcp_dp := ρ_nat.data.dstPort;
    meta.tcp_dp.init := 1
  } [] {
    // nat_no_nat
    assume ρ_nat.action = 5;
    meta.do_forward := 1;
    meta.do_forward.init := 1;
  }
} [] { // miss
  assume γ_nat.miss == 1
};

assert meta.do_forward.init == 1;
assert ipv4.ttl.init == 1;

{ // ipv4_lpm
  assume meta.do_forward == 1 ∧ ipv4.ttl > 0;
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
    assume standard_metadata.egress_port == γ_send_frame.standard_metadata.egress_port;
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
      assume γ_send_to_cpu.miss == 0;
      assume γ_send_to_cpu.hitAction == ρ_send_to_cpu.id;
      // do_cpu_encap
      assume ρ_send_to_cpu.action = 0;
      cpu_header.isValid := 1;
      cpu_header.preamble.init := 1;
      cpu_header.device.init := 1;
      cpu_header.reason.init := 1;
      cpu_header.if_index.init := 1;
      
      cpu_header.preamble := 0;
      cpu_header.device := 0;
      cpu_header.device := 0xab;
      assert meta.if_index.init == 1;
      cpu_header.if_index := meta.if_index;
    } [] {
      // miss
      assume γ_send_to_cpu.miss == 1
    }
  }
}
```




### Computing the Weakest Precondition



First Compute the weakest precondition of egress.

```
ϕₑ ≜
standard_metadata.egress_spec != DROP ⇒ (
 (standard_metadata.instance_type == 0 ⇒
   (standard_metadata.egress_spec == γ_send_frame.standard_metadata.egress_port) ⇒
      ( (standard_metadata.egress_spec == ρ_send_frame.standard_metadata.egress_port
         ∧ γ_send_frame.miss == 0
         ∧ γ_forward.hitAction = ρ_send_frame.id
         ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                       ∧ meta.ipv4_da.init == 1 
                                       ∧ meta.tcp_sp.init == 1
                                       ∧ meta.tcp_dp.init == 1))))
  ∧
  standard_metadata.instance_type != 0 ⇒
    (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ assume ρ_send_frame.action = 0 ⇒
       (meta.if_index.init == 1))
)
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
   ⇒ (ρ_forward.action == 0 ⇒ \phi_e))
  ∧
  (γ_forward.miss == 1 ⇒ ϕₑ))
  
=== 
meta.nhop_ipv4.init == 1 ∧
(γ_forward.meta.nhop_ipv4 == meta.nhop_ipv4 ⇒
  ((meta.nhop_ipv4 == ρ_forward.nhop_ipv4
    ∧ γ_forward.miss == 0
    ∧ γ_forward.hitAction = ρ_forward.id)
   ⇒ 
   (ρ_forward.action == 0 ⇒ 
     (standard_metadata.egress_spec != DROP ⇒ (
       (standard_metadata.instance_type == 0 ⇒
         (standard_metadata.egress_spec == γ_send_frame.standard_metadata.egress_port) ⇒
            ( (standard_metadata.egress_spec == ρ_send_frame.standard_metadata.egress_port
               ∧ γ_send_frame.miss == 0
               ∧ γ_forward.hitAction = ρ_send_frame.id
               ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                             ∧ meta.ipv4_da.init == 1 
                                             ∧ meta.tcp_sp.init == 1
                                             ∧ meta.tcp_dp.init == 1))))
       ∧
       (standard_metadata.instance_type != 0 ⇒
          (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
              (meta.if_index.init == 1))))))
  ∧
  (γ_forward.miss == 1 ⇒ 
     (standard_metadata.egress_spec != DROP ⇒ (
       (standard_metadata.instance_type == 0 ⇒
         (standard_metadata.egress_spec == γ_send_frame.standard_metadata.egress_port) ⇒
            ( (standard_metadata.egress_spec == ρ_send_frame.standard_metadata.egress_port
               ∧ γ_send_frame.miss == 0
               ∧ γ_forward.hitAction = ρ_send_frame.id
               ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                             ∧ meta.ipv4_da.init == 1 
                                             ∧ meta.tcp_sp.init == 1
                                             ∧ meta.tcp_dp.init == 1))))
       ∧
       (standard_metadata.instance_type != 0 ⇒
          (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
              (meta.if_index.init == 1)))))))
  
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
   ⇒ (ρ_forward.action == 0 ⇒ ϕₑ[ρ_ipv4_lpm.port/standard_metadata.egress_spec])
   )
  ∧
  (γ_forward.miss == 1 ⇒ ϕₑ[ρ_ipv4_lpm.port/standard_metadata.egress_spec]))
```


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
γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
     (ipv4.ttl.init == 1 ∧ 
         ϕ_f[ρ_ipv4_lpm.port / standard_metadata.egress_spec]
            [ρ_ipv4_lpm.nhop_ivp4 / meta.nhop_ivp4]
            [1 / meta.nhop_ipv4.init]))
     ∧ 
     (ρ_ipv4_lpm.action == 1 ⇒ ϕ_f[DROP/standard_metadata.egress_spec] ))
```

Note that 

```
ϕ_f[ρ_ipv4_lpm.port / standard_metadata.egress_spec]
   [ρ_ipv4_lpm.nhop_ivp4 / meta.nhop_ivp4]
   [1 / meta.nhop_ipv4.init]
=== 
(γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
  ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
    ∧ γ_forward.miss == 0
    ∧ γ_forward.hitAction = ρ_forward.id)
   ⇒ 
   (ρ_forward.action == 0 ⇒ 
     (ρ_ipv4_lpm.port != DROP ⇒ (
       (standard_metadata.instance_type == 0 ⇒
         (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
            ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
               ∧ γ_send_frame.miss == 0
               ∧ γ_forward.hitAction = ρ_send_frame.id
               ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                             ∧ meta.ipv4_da.init == 1 
                                             ∧ meta.tcp_sp.init == 1
                                             ∧ meta.tcp_dp.init == 1))))
       ∧
       (standard_metadata.instance_type != 0 ⇒
          (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
              (meta.if_index.init == 1))))))
  ∧
  (γ_forward.miss == 1 ⇒ 
     (ρ_ipv4_lpm.port != DROP ⇒ (
       (standard_metadata.instance_type == 0 ⇒
         (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
            ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
               ∧ γ_send_frame.miss == 0
               ∧ γ_forward.hitAction = ρ_send_frame.id
               ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                             ∧ meta.ipv4_da.init == 1 
                                             ∧ meta.tcp_sp.init == 1
                                             ∧ meta.tcp_dp.init == 1))))
       ∧
       (standard_metadata.instance_type != 0 ⇒
          (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
              (meta.if_index.init == 1)))))))
```

and

```
ϕ_f[DROP/standard_metadata.egress_spec]
===
meta.nhop_ipv4.init == 1
```

so 
```
ϕ_ipv4_lpm
=== 
γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
  ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
  ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
        meta.ipv4_da.init == 1
        ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
           ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
               ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                    (ipv4.ttl.init == 1 ∧ 
                     (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                      ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                       ∧ γ_forward.miss == 0
                       ∧ γ_forward.hitAction = ρ_forward.id)
                       ⇒ 
                        (ρ_forward.action == 0 ⇒ 
                          (ρ_ipv4_lpm.port != DROP ⇒ (
                            (standard_metadata.instance_type == 0 ⇒
                             (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                               ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                 ∧ γ_send_frame.miss == 0
                                 ∧ γ_forward.hitAction = ρ_send_frame.id
                                 ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                               ∧ meta.ipv4_da.init == 1 
                                                               ∧ meta.tcp_sp.init == 1
                                                               ∧ meta.tcp_dp.init == 1))))
                            ∧
                            (standard_metadata.instance_type != 0 ⇒
                              (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                         (meta.if_index.init == 1)))))))
                      ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                            (standard_metadata.instance_type == 0 ⇒
                               (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                 ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                   ∧ γ_send_frame.miss == 0
                                   ∧ γ_forward.hitAction = ρ_send_frame.id
                                   ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                 ∧ meta.ipv4_da.init == 1 
                                                                 ∧ meta.tcp_sp.init == 1
                                                                 ∧ meta.tcp_dp.init == 1))))
                            ∧
                            (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                 (meta.if_index.init == 1)))))))))
                   ∧ 
                   (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 )))))
```


And the if-statement produces the following (no short-circuting, for simplicity):

```
ϕ_b ≜
 meta.do_forward.init == 1 ∧ ipv4.ttl.init == 1 ∧
 ( meta.do_forward == 1 ∧ ipv4.ttl > 0 ⇒ ϕ_ipv4_lpm
 ∧ ¬ (meta.do_forward == 1 ∧ ipv4.ttl > 0) ⇒ ϕₑ
===
meta.do_forward.init == 1 ∧ ipv4.ttl.init == 1 ∧
(meta.do_forward == 1 ∧ ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         meta.ipv4_da.init == 1
         ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                ∧ meta.ipv4_da.init == 1 
                                                                ∧ meta.tcp_sp.init == 1
                                                                ∧ meta.tcp_dp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                  ∧ meta.ipv4_da.init == 1 
                                                                  ∧ meta.tcp_sp.init == 1
                                                                  ∧ meta.tcp_dp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))
∧ ¬ (meta.do_forward == 1 ∧ ipv4.ttl > 0) ⇒ (standard_metadata.egress_spec != DROP ⇒ (
 (standard_metadata.instance_type == 0 ⇒
   (standard_metadata.egress_spec == γ_send_frame.standard_metadata.egress_port) ⇒
      ( (standard_metadata.egress_spec == ρ_send_frame.standard_metadata.egress_port
         ∧ γ_send_frame.miss == 0
         ∧ γ_forward.hitAction = ρ_send_frame.id
         ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                       ∧ meta.ipv4_da.init == 1 
                                       ∧ meta.tcp_sp.init == 1
                                       ∧ meta.tcp_dp.init == 1))))
  ∧
  standard_metadata.instance_type != 0 ⇒
    (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
       (meta.if_index.init == 1))))
```

Now, push `ϕ_b` through `nat` and `if_info`

The miss case is 

```
ϕ_nat_miss ≜ γ_nat.miss == 1 ⇒ ϕ_b
===
γ_nat.miss == 1 ⇒
meta.do_forward.init == 1 ∧ ipv4.ttl.init == 1 ∧
(meta.do_forward == 1 ∧ ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         meta.ipv4_da.init == 1
         ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                ∧ meta.ipv4_da.init == 1 
                                                                ∧ meta.tcp_sp.init == 1
                                                                ∧ meta.tcp_dp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                  ∧ meta.ipv4_da.init == 1 
                                                                  ∧ meta.tcp_sp.init == 1
                                                                  ∧ meta.tcp_dp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))
∧ ¬ (meta.do_forward == 1 ∧ ipv4.ttl > 0) ⇒ (standard_metadata.egress_spec != DROP ⇒ (
 (standard_metadata.instance_type == 0 ⇒
   (standard_metadata.egress_spec == γ_send_frame.standard_metadata.egress_port) ⇒
      ( (standard_metadata.egress_spec == ρ_send_frame.standard_metadata.egress_port
         ∧ γ_send_frame.miss == 0
         ∧ γ_forward.hitAction = ρ_send_frame.id
         ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                       ∧ meta.ipv4_da.init == 1 
                                       ∧ meta.tcp_sp.init == 1
                                       ∧ meta.tcp_dp.init == 1))))
  ∧
  standard_metadata.instance_type != 0 ⇒
    (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
       (meta.if_index.init == 1))))
```

The `nat_no_nat` case is

```
ρ_nat.action == 5 ⇒ ϕ_b[1 / meta.do_forward, 1 / meta.do_forward.init]
===
ρ_nat.action == 5 ⇒
γ_nat.miss == 1 ⇒
ipv4.ttl.init == 1 ∧
(ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         meta.ipv4_da.init == 1
         ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                ∧ meta.ipv4_da.init == 1 
                                                                ∧ meta.tcp_sp.init == 1
                                                                ∧ meta.tcp_dp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                  ∧ meta.ipv4_da.init == 1 
                                                                  ∧ meta.tcp_sp.init == 1
                                                                  ∧ meta.tcp_dp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))
```

The `nat_hit_ext_to_int` case is

```
ρ_nat.action == 4 ⇒ ϕ_b[ 1 / meta.do_forward
                        , 1 / meta.do_forward.init
                        , ρ_nat.data.dstAddr / meta.ipv4_da
                        , 1 / meta.ipv4_da.init
                        , ρ_nat.data.dstPort / meta.tcp_dp
                        , 1 / meta.tcp_dp.init]
===
ρ_nat.action == 4 ⇒ 
γ_nat.miss == 1 ⇒
ipv4.ttl.init == 1 ∧
(ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da == ρ_nat.data.dstAddr ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         ∧ (ρ_nat.data.dstAddr & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                ∧ meta.tcp_sp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                  ∧ meta.tcp_sp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))

```

The `nat_hit_int_to_ext` case is

```
ρ_nat.action == 3 ⇒ ϕ_b[ 1 / meta.do_forward
                        , 1 / meta.do_forward.init
                        , ρ_nat.data.srcAddr / meta.ipv4_sa
                        , 1 / meta.ipv4_sa.init
                        , ρ_nat.data.srcPort / meta.tcp_sp
                        , 1 / meta.tcp_sp.init]
===
ρ_nat.action == 3 ⇒ 
γ_nat.miss == 1 ⇒
ipv4.ttl.init == 1 ∧
(ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         meta.ipv4_da.init == 1
         ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_da.init == 1 
                                                                ∧ meta.tcp_dp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_da.init == 1 
                                                                  ∧ meta.tcp_dp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))
```

The `nat_miss_ext_to_int` case is

```
ρ_nat.action == 2 ⇒ ϕ_b[ 0 / meta.do_forward
                        , DROP / standard_metadata.egress_spec]
==
⊤
```


The `nat_miss_int_to_ext` case is

```
ρ_nat.action == 1 ⇒ ϕ_b[ 0 / meta.do_forward
                        , CLONE / standard_metadata.instance_type]
===
ρ_nat.action == 1 ⇒
  (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
       (meta.if_index.init == 1))
```

The `_drop` case is

```
ρ_nat.action == 0 ⇒ ϕ_b[ DROP / standard_metadata.egress_spec ]
===
ρ_nat.action == 0 ⇒
meta.do_forward.init == 1 ∧ ipv4.ttl.init == 1 ∧
(meta.do_forward == 1 ∧ ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         meta.ipv4_da.init == 1
         ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                ∧ meta.ipv4_da.init == 1 
                                                                ∧ meta.tcp_sp.init == 1
                                                                ∧ meta.tcp_dp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                  ∧ meta.ipv4_da.init == 1 
                                                                  ∧ meta.tcp_sp.init == 1
                                                                  ∧ meta.tcp_dp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))
```


Let the conjuction of these actions be called `ϕ_nat_acts_inner`
and 
```
ϕ_nat_acts ≜ 
(γ_nat.miss == 0 ∧ γ_nat.hitAction == ρ_nat.id) ⇒ ϕ_nat_acts_inner
=====
(γ_nat.miss == 0 ∧ γ_nat.hitAction == ρ_nat.id) ⇒ (
(// _drop
ρ_nat.action == 0 ⇒
meta.do_forward.init == 1 ∧ ipv4.ttl.init == 1 ∧
(meta.do_forward == 1 ∧ ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         meta.ipv4_da.init == 1
         ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                ∧ meta.ipv4_da.init == 1 
                                                                ∧ meta.tcp_sp.init == 1
                                                                ∧ meta.tcp_dp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                  ∧ meta.ipv4_da.init == 1 
                                                                  ∧ meta.tcp_sp.init == 1
                                                                  ∧ meta.tcp_dp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧  ρ_send_frame.action = 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))
) ∧  ( // nat_miss_int_to_ext
ρ_nat.action == 1 ⇒
  (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
       (meta.if_index.init == 1))
) ∧ ( // nat_miss_ext_to_int
  ⊤
) \wedge ( // nat_hit_int_to_ext
ρ_nat.action == 3 ⇒ 
γ_nat.miss == 1 ⇒
ipv4.ttl.init == 1 ∧
(ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         meta.ipv4_da.init == 1
         ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_da.init == 1 
                                                                ∧ meta.tcp_dp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_da.init == 1 
                                                                  ∧ meta.tcp_dp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action = 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))
) ∧ ( // nat_hit_ext_to_int
ρ_nat.action == 4 ⇒ 
γ_nat.miss == 1 ⇒
ipv4.ttl.init == 1 ∧
(ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da == ρ_nat.data.dstAddr ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         ∧ (ρ_nat.data.dstAddr & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                ∧ meta.tcp_sp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                  ∧ meta.tcp_sp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))



) ∧ (// nat_no_nat
ρ_nat.action == 5 ⇒
γ_nat.miss == 1 ⇒
ipv4.ttl.init == 1 ∧
(ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         meta.ipv4_da.init == 1
         ∧ (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                ∧ meta.ipv4_da.init == 1 
                                                                ∧ meta.tcp_sp.init == 1
                                                                ∧ meta.tcp_dp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                  ∧ meta.ipv4_da.init == 1 
                                                                  ∧ meta.tcp_sp.init == 1
                                                                  ∧ meta.tcp_dp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 )))))))
)
```


So the hit case is
```
ϕ_nat_hit ≜
meta.is_ext_if == ρ_nat.meta.is_ext_if 
∧ ipv4.isValid == ρ_nat.ipv4.isValid
∧ tcp.isValid = ρ_nat.tcp.isValid
⇒ ϕ₄

where
  ϕ₄ ≜
  (ρ_nat.ipv4.srcAddrMask != 0 ⇒ 
       (ipv4.srcAddr.init == 1 
        ∧ (ipv4.srcAddr & ρ_nat.ipv4.srcAddrMask = ρ_nat.ipv4.srcAddr & ρ_nat.ipv4.srcAddrMask  ⇒ ϕ₃)))
    ∧ (ρ_nat.ipv4.srcAddrMask == 0 ⇒ ϕ₃)
  ϕ₃ ≜
    (ρ_nat.ipv4.dstAddrMask != 0 ⇒ 
       (ipv4.dstAddr.init == 1 
        ∧ (ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask = ρ_nat.ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask  ⇒ ϕ₂)))
    ∧ (ρ_nat.ipv4.dstAddrMask == 0 ⇒ ϕ₂)
    
  ϕ₂ ≜
    (ρ_nat.tcp.srcPortMask != 0 ⇒ 
       tcp.srcPort.init = 1 
       ∧ (tcp.srcPort & ρ_nat.tcp.srcPortMask = ρ_nat.tcp.srcPort & ρ_nat.tcp.srcPortMask
          ⇒ ϕ₁))
    ∧ (ρ_nat.tcp.srcPortMask == 0 ⇒ ϕ₁)
  ϕ₁ ≜
  (ρ_nat.tcp.dstPortMask != 0 ⇒ 
     tcp.dstPort.init == 1 ∧ (tcp.dstPort & ρ_nat.tcp.dstPortMask = ρ_nat.tcp.dstPort & ρ_nat.tcp.dstPortMask ⇒ ϕ_nat_acts_inner))
  ∧ (ρ_nat.tcp.dstPortMask == 0 ⇒ ϕ_nat_acts)
  
======
(meta.is_ext_if == ρ_nat.meta.is_ext_if 
 ∧ ipv4.isValid == ρ_nat.ipv4.isValid
 ∧ tcp.isValid = ρ_nat.tcp.isValid) ⇒ (

  (ρ_nat.ipv4.srcAddrMask != 0 ⇒ 
     (ipv4.srcAddr.init == 1 
     ∧ (ipv4.srcAddr & ρ_nat.ipv4.srcAddrMask = ρ_nat.ipv4.srcAddr & ρ_nat.ipv4.srcAddrMask  ⇒
         (ρ_nat.ipv4.dstAddrMask != 0 ⇒ 
           (ipv4.dstAddr.init == 1 
           ∧ (ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask = ρ_nat.ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask ⇒
              (ρ_nat.tcp.srcPortMask != 0 ⇒ 
                (tcp.srcPort.init = 1 
                ∧ (tcp.srcPort & ρ_nat.tcp.srcPortMask = ρ_nat.tcp.srcPort & ρ_nat.tcp.srcPortMask ⇒ 
                    (ρ_nat.tcp.dstPortMask != 0 ⇒ 
                      tcp.dstPort.init == 1 
                      ∧ (tcp.dstPort & ρ_nat.tcp.dstPortMask = ρ_nat.tcp.dstPort & ρ_nat.tcp.dstPortMask ⇒ 
                          ϕ_nat_acts_inner))
                    ∧ (ρ_nat.tcp.dstPortMask == 0 ⇒ ϕ_nat_acts))))
              ∧ (ρ_nat.tcp.srcPortMask == 0 ⇒
                 (ρ_nat.tcp.dstPortMask != 0 ⇒ 
                   tcp.dstPort.init == 1 ∧ (tcp.dstPort & ρ_nat.tcp.dstPortMask = ρ_nat.tcp.dstPort & ρ_nat.tcp.dstPortMask ⇒ 
                     ϕ_nat_acts_inner))
                 ∧ (ρ_nat.tcp.dstPortMask == 0 ⇒ ϕ_nat_acts)))))
          ∧ (ρ_nat.ipv4.dstAddrMask == 0 ⇒ 
              (ρ_nat.tcp.srcPortMask != 0 ⇒ 
               tcp.srcPort.init = 1 
               ∧ (tcp.srcPort & ρ_nat.tcp.srcPortMask = ρ_nat.tcp.srcPort & ρ_nat.tcp.srcPortMask ⇒ ϕ₁))
              ∧ (ρ_nat.tcp.srcPortMask == 0 ⇒ 
                  (ρ_nat.tcp.dstPortMask != 0 ⇒ 
                    tcp.dstPort.init == 1 ∧ (tcp.dstPort & ρ_nat.tcp.dstPortMask = ρ_nat.tcp.dstPort & ρ_nat.tcp.dstPortMask ⇒
                      ϕ_nat_acts_inner))
                  ∧ (ρ_nat.tcp.dstPortMask == 0 ⇒ ϕ_nat_acts)))))
  ∧ (ρ_nat.ipv4.srcAddrMask == 0 ⇒
        (ρ_nat.ipv4.dstAddrMask != 0 ⇒ 
          (ipv4.dstAddr.init == 1 
           ∧ (ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask = ρ_nat.ipv4.dstAddr & ρ_nat.ipv4.dstAddrMask  ⇒ 
              ((ρ_nat.tcp.srcPortMask != 0 ⇒ 
               tcp.srcPort.init = 1 
               ∧ (tcp.srcPort & ρ_nat.tcp.srcPortMask = ρ_nat.tcp.srcPort & ρ_nat.tcp.srcPortMask ⇒ 
                 ((ρ_nat.tcp.dstPortMask != 0 ⇒ 
                   tcp.dstPort.init == 1 ∧ (tcp.dstPort & ρ_nat.tcp.dstPortMask = ρ_nat.tcp.dstPort & ρ_nat.tcp.dstPortMask ⇒ 
                     ϕ_nat_acts_inner))
                  ∧ (ρ_nat.tcp.dstPortMask == 0 ⇒ ϕ_nat_acts)))
          ∧ (ρ_nat.tcp.srcPortMask == 0 ⇒ ϕ₁)))))
        ∧ (ρ_nat.ipv4.dstAddrMask == 0 ⇒ 
           (ρ_nat.tcp.srcPortMask != 0 ⇒ 
            tcp.srcPort.init = 1 
            ∧ (tcp.srcPort & ρ_nat.tcp.srcPortMask = ρ_nat.tcp.srcPort & ρ_nat.tcp.srcPortMask ⇒  
                 ((ρ_nat.tcp.dstPortMask != 0 ⇒ 
                   tcp.dstPort.init == 1 ∧ (tcp.dstPort & ρ_nat.tcp.dstPortMask = ρ_nat.tcp.dstPort & ρ_nat.tcp.dstPortMask ⇒ 
                     ϕ_nat_acts_inner))
                  ∧ (ρ_nat.tcp.dstPortMask == 0 ⇒ ϕ_nat_acts))))
           ∧ (ρ_nat.tcp.srcPortMask == 0 ⇒  
                 ((ρ_nat.tcp.dstPortMask != 0 ⇒ 
                   tcp.dstPort.init == 1 ∧ (tcp.dstPort & ρ_nat.tcp.dstPortMask = ρ_nat.tcp.dstPort & ρ_nat.tcp.dstPortMask ⇒ 
                     ϕ_nat_acts_inner))
                  ∧ (ρ_nat.tcp.dstPortMask == 0 ⇒ ϕ_nat_acts))))))
)                  
```

At this point its not tenable to copy `ϕ_nat_acts` over and over, so we'll do it once at the end.

Which means that the condition at the application of `nat` is:

```
ϕ_nat ≜
( γ_nat.meta.is_ext_if = meta.is_ext_if
  ∧ γ_nat.meta.ipv4.isValid = ipv4.isValid
  ∧ γ_nat.meta.tcp.isValid = tcp.isValid
  ∧ γ_nat.ipv4.srcAddr = ipv4.srcAddr
  ∧ γ_nat.ipv4.dstAddr = ipv4.dstAddr
  ∧ γ_nat.tcp.srcPort = tcp.srcPort
  ∧ γ_nat.tcp.dstPort = tcp.dstPort
  ∧ meta.is_ext_if.init == 1
) ⇒ ( 
  ϕ_nat_hit ∧ ϕ_nat_miss
)
```


Now we push `ϕ_nat` through `if_info`:

The miss case is:

```
ϕ_if_info_miss ≜ γ_if_info.miss == 1 ⇒ ϕ_nat 
```

The `set_if_info` case is

```
ϕ_set_if_info ≜
ρ_if_info.action == 1
⇒ 
 (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
       , 1 / meta.if_ipv4_addr.init
       , ρ_if_info.data.mac_addr / meta.if_mac_addr
       , 1 / meta.if_mac_addr.init
       , ρ_if_info.data.is_ext / meta.is_ext_if
       , 1 / meta.is_ext_if.init])
```

The `_drop` case is

```
ϕ_if_info_drop ≜ ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec])
```

Which means that the condition for ingress and egress processing is

```
ϕᵢ ≜
meta.if_index.init == 1
∧
(γ_if_info.meta.if_index == meta.if_index ⇒ (
  ((ρ_if_info.meta.if_index == meta.if_index
   ∧ γ_if_info.miss == 0
   ∧ γ_if_info.hitAction == ρ_if_info.id)
   ⇒ (ϕ_set_if_info ∧ ϕ_if_info_drop)
   )
  ∧ 
  ϕ_if_info_miss
))

===
meta.if_index.init == 1
∧
(γ_if_info.meta.if_index == meta.if_index ⇒ (
  ((ρ_if_info.meta.if_index == meta.if_index
   ∧ γ_if_info.miss == 0
   ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
      (ρ_if_info.action == 1 ⇒ 
       (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
             , 1 / meta.if_ipv4_addr.init
             , ρ_if_info.data.mac_addr / meta.if_mac_addr
             , 1 / meta.if_mac_addr.init
             , ρ_if_info.data.is_ext / meta.is_ext_if
             , 1 / meta.is_ext_if.init])
       ) ∧ (
       ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec])
       ))
   )
  ∧ 
  (γ_if_info.miss == 1 ⇒ ϕ_nat)
))


```

Now we pass this condition through the implementation of the parser. 

First we pass it through the TCP parsing block:

```
ϕ_tcp ≜ 
( ipv4.protocol == IP_PROT_TCP ⇒ (
     ϕᵢ[1 / tcp.isValid, 1 / tcp.*.init
       , tcp.srcPort / meta.tcp_sp, 1 / meta.tcp_sp.init
       , tcp.dstPort / meta.tcp_dp, 1 / meta.tcp_dp.init ]
   )
) ∧ ipv4.protocol != IP_PROT_TCP ⇒ ϕᵢ
===
( ipv4.protocol == IP_PROT_TCP ⇒ (
  (meta.if_index.init == 1
  ∧
  (γ_if_info.meta.if_index == meta.if_index ⇒ (
    ((ρ_if_info.meta.if_index == meta.if_index
     ∧ γ_if_info.miss == 0
     ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / tcp.isValid
               , 1 / tcp.*.init
               , tcp.srcPort / meta.tcp_sp
               , 1 / meta.tcp_sp.init
               , tcp.dstPort / meta.tcp_dp
               , 1 / meta.tcp_dp.init ])
         ) ∧ (
         ρ_if_info.action == 0 ⇒ (
           ϕ_nat[DROP / standard_metadata.egress_spec]
                [ 1 / tcp.isValid 
                , 1 / tcp.*.init
                , tcp.srcPort / meta.tcp_sp
                , 1 / meta.tcp_sp.init
                , tcp.dstPort / meta.tcp_dp
                , 1 / meta.tcp_dp.init ])
         )
    )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat))))
)) 
∧ (ipv4.protocol != IP_PROT_TCP ⇒ 
   (meta.if_index.init == 1
   ∧
   (γ_if_info.meta.if_index == meta.if_index ⇒ (
     ((ρ_if_info.meta.if_index == meta.if_index
      ∧ γ_if_info.miss == 0
      ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init])
       ) ∧ (
         ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec])
       )
     )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat)))))
```

Then through IPV4

```
ϕ_ipv4 ≜
(
  ethernet.etherType == ETHERTYPE_IPV4 ⇒
  ((( ipv4.protocol == IP_PROT_TCP ⇒ (
  (meta.if_index.init == 1
  ∧
  (γ_if_info.meta.if_index == meta.if_index ⇒ (
    ((ρ_if_info.meta.if_index == meta.if_index
     ∧ γ_if_info.miss == 0
     ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / tcp.isValid
               , 1 / tcp.*.init
               , tcp.srcPort / meta.tcp_sp
               , 1 / meta.tcp_sp.init
               , tcp.dstPort / meta.tcp_dp
               , 1 / meta.tcp_dp.init ]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ])
         ) ∧ (
         ρ_if_info.action == 0 ⇒ (
           ϕ_nat[DROP / standard_metadata.egress_spec]
                [ 1 / tcp.isValid 
                , 1 / tcp.*.init
                , tcp.srcPort / meta.tcp_sp
                , 1 / meta.tcp_sp.init
                , tcp.dstPort / meta.tcp_dp
                , 1 / meta.tcp_dp.init ]
                [ 1 / ipv4.isValid
                , 1 / ipv4.*.init
                , ipv4.srcAddr / meta.ipv4_sa
                , 1 / meta.ipv4_sa
                , ipv4.dstAddr / meta.ipv4_da
                , 1 / meta.ipv4_da.init
                , ipv4.totalLen - 20 / meta.tcpLength
                , 1 / meta.tcpLength.init ])
         )
    )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat))))
)) 
∧ (ipv4.protocol != IP_PROT_TCP ⇒ 
   (meta.if_index.init == 1
   ∧
   (γ_if_info.meta.if_index == meta.if_index ⇒ (
     ((ρ_if_info.meta.if_index == meta.if_index
      ∧ γ_if_info.miss == 0
      ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ])
       ) ∧ (
         ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec]
                                       [ 1 / ipv4.isValid
                                       , 1 / ipv4.*.init
                                       , ipv4.srcAddr / meta.ipv4_sa
                                       , 1 / meta.ipv4_sa
                                       , ipv4.dstAddr / meta.ipv4_da
                                       , 1 / meta.ipv4_da.init
                                       , ipv4.totalLen - 20 / meta.tcpLength
                                       , 1 / meta.tcpLength.init ])
       )
     )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat))))))
  )

) ∧ ethernet.etherType != ETHERTYPE_IPV4 ⇒(
meta.if_index.init == 1
∧
(γ_if_info.meta.if_index == meta.if_index ⇒ (
  ((ρ_if_info.meta.if_index == meta.if_index
   ∧ γ_if_info.miss == 0
   ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
      (ρ_if_info.action == 1 ⇒ 
       (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
             , 1 / meta.if_ipv4_addr.init
             , ρ_if_info.data.mac_addr / meta.if_mac_addr
             , 1 / meta.if_mac_addr.init
             , ρ_if_info.data.is_ext / meta.is_ext_if
             , 1 / meta.is_ext_if.init])
       ) ∧ (
       ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec])
       ))
   )
  ∧ 
  (γ_if_info.miss == 1 ⇒ ϕ_nat)
)))

```

and finally through ethernet and CPU

```
ϕₚ ≜
pkt.lookahead == 0 ⇒ (
  ((
  ethernet.etherType == ETHERTYPE_IPV4 ⇒
  ((( ipv4.protocol == IP_PROT_TCP ⇒ (
  ((γ_if_info.meta.if_index == cpu_header.if_index  ⇒ (
    ((ρ_if_info.meta.if_index == cpu_header.if_index 
     ∧ γ_if_info.miss == 0
     ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / tcp.isValid
               , 1 / tcp.*.init
               , tcp.srcPort / meta.tcp_sp
               , 1 / meta.tcp_sp.init
               , tcp.dstPort / meta.tcp_dp
               , 1 / meta.tcp_dp.init ]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ]
               [ 1 / cpu_header.*.init
               , pkt.lookahead / cpu_header.preamble
               , cpu_header.if_index / meta.if_index
               , 1 / meta.if_index.init
               , 1 / ethernet.isValid
               , 1 / ethernet.*.init ])
         ) ∧ (
         ρ_if_info.action == 0 ⇒ (
           ϕ_nat[DROP / standard_metadata.egress_spec]
                [ 1 / tcp.isValid 
                , 1 / tcp.*.init
                , tcp.srcPort / meta.tcp_sp
                , 1 / meta.tcp_sp.init
                , tcp.dstPort / meta.tcp_dp
                , 1 / meta.tcp_dp.init ]
                [ 1 / ipv4.isValid
                , 1 / ipv4.*.init
                , ipv4.srcAddr / meta.ipv4_sa
                , 1 / meta.ipv4_sa
                , ipv4.dstAddr / meta.ipv4_da
                , 1 / meta.ipv4_da.init
                , ipv4.totalLen - 20 / meta.tcpLength
                , 1 / meta.tcpLength.init ]
                [ 1 / cpu_header.*.init
                , pkt.lookahead / cpu_header.preamble
                , cpu_header.if_index / meta.if_index
                , 1 / meta.if_index.init
                , 1 / ethernet.isValid
                , 1 / ethernet.*.init ])
         )
    )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat[ 1 / cpu_header.*.init
                                , pkt.lookahead / cpu_header.preamble
                                , cpu_header.if_index / meta.if_index
                                , 1 / meta.if_index.init
                                , 1 / ethernet.isValid
                                , 1 / ethernet.*.init ]))))
)) 
∧ (ipv4.protocol != IP_PROT_TCP ⇒ 
   ((γ_if_info.meta.if_index == cpu_header.if_index ⇒ (
     ((ρ_if_info.meta.if_index == cpu_header.if_index 
      ∧ γ_if_info.miss == 0
      ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ]
               [ 1 / cpu_header.*.init
               , pkt.lookahead / cpu_header.preamble
               , cpu_header.if_index / meta.if_index
               , 1 / meta.if_index.init
               , 1 / ethernet.isValid
               , 1 / ethernet.*.init ])
       ) ∧ (
         ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec]
                                       [ 1 / ipv4.isValid
                                       , 1 / ipv4.*.init
                                       , ipv4.srcAddr / meta.ipv4_sa
                                       , 1 / meta.ipv4_sa
                                       , ipv4.dstAddr / meta.ipv4_da
                                       , 1 / meta.ipv4_da.init
                                       , ipv4.totalLen - 20 / meta.tcpLength
                                       , 1 / meta.tcpLength.init ]
                                       [ 1 / cpu_header.*.init
                                       , pkt.lookahead / cpu_header.preamble
                                       , cpu_header.if_index / meta.if_index
                                       , 1 / meta.if_index.init
                                       , 1 / ethernet.isValid
                                       , 1 / ethernet.*.init ])
       )
     )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat[ 1 / cpu_header.*.init
                                , pkt.lookahead / cpu_header.preamble
                                , cpu_header.if_index / meta.if_index
                                , 1 / meta.if_index.init
                                , 1 / ethernet.isValid
                                , 1 / ethernet.*.init ]))))))
  )

) ∧ ethernet.etherType != ETHERTYPE_IPV4 ⇒(
(γ_if_info.meta.if_index == cpu_header.if_index ⇒ (
  ((ρ_if_info.meta.if_index == cpu_header.if_index 
   ∧ γ_if_info.miss == 0
   ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
      (ρ_if_info.action == 1 ⇒ 
       (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
             , 1 / meta.if_ipv4_addr.init
             , ρ_if_info.data.mac_addr / meta.if_mac_addr
             , 1 / meta.if_mac_addr.init
             , ρ_if_info.data.is_ext / meta.is_ext_if
             , 1 / meta.is_ext_if.init]
             [ 1 / cpu_header.*.init
             , pkt.lookahead / cpu_header.preamble
             , cpu_header.if_index / meta.if_index
             , 1 / meta.if_index.init
             , 1 / ethernet.isValid
             , 1 / ethernet.*.init ])
       ) ∧ (
       ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec]
                                     [ 1 / cpu_header.*.init
                                     , pkt.lookahead / cpu_header.preamble
                                     , cpu_header.if_index / meta.if_index
                                     , 1 / meta.if_index.init
                                     , 1 / ethernet.isValid
                                     , 1 / ethernet.*.init ])
      )
   )
  )
  ∧ 
  (γ_if_info.miss == 1 ⇒ ϕ_nat [ 1 / cpu_header.*.init
                                , pkt.lookahead / cpu_header.preamble
                                , cpu_header.if_index / meta.if_index
                                , 1 / meta.if_index.init
                                , 1 / ethernet.isValid
                                , 1 / ethernet.*.init ])
)))))
∧ pkt.lookahead != 0 ⇒ (
  (ethernet.dstAddr == pkt.lookahead[0:48];
  ∧ ethernet.srcAddr[0:16] == ethernet.srcAddr[0:16])
  ⇒ ((
  ethernet.etherType == ETHERTYPE_IPV4 ⇒
  ((( ipv4.protocol == IP_PROT_TCP ⇒ (
  (meta.if_index.init == 1
  ∧
  (γ_if_info.meta.if_index == meta.if_index ⇒ (
    ((ρ_if_info.meta.if_index == meta.if_index
     ∧ γ_if_info.miss == 0
     ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / tcp.isValid
               , 1 / tcp.*.init
               , tcp.srcPort / meta.tcp_sp
               , 1 / meta.tcp_sp.init
               , tcp.dstPort / meta.tcp_dp
               , 1 / meta.tcp_dp.init ]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ]
               [ 1 / ethernet.isValid
               , 1 / ethernet.*.init ])
         ) ∧ (
         ρ_if_info.action == 0 ⇒ (
           ϕ_nat[DROP / standard_metadata.egress_spec]
                [ 1 / tcp.isValid 
                , 1 / tcp.*.init
                , tcp.srcPort / meta.tcp_sp
                , 1 / meta.tcp_sp.init
                , tcp.dstPort / meta.tcp_dp
                , 1 / meta.tcp_dp.init ]
                [ 1 / ipv4.isValid
                , 1 / ipv4.*.init
                , ipv4.srcAddr / meta.ipv4_sa
                , 1 / meta.ipv4_sa
                , ipv4.dstAddr / meta.ipv4_da
                , 1 / meta.ipv4_da.init
                , ipv4.totalLen - 20 / meta.tcpLength
                , 1 / meta.tcpLength.init ]
                [ 1 / ethernet.isValid
                , 1 / ethernet.*.init ])
         )
    )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat[ 1 / ethernet.isValid, 1 / ethernet.*.init ]))))
)) 
∧ (ipv4.protocol != IP_PROT_TCP ⇒ 
   (meta.if_index.init == 1
   ∧
   (γ_if_info.meta.if_index == meta.if_index ⇒ (
     ((ρ_if_info.meta.if_index == meta.if_index
      ∧ γ_if_info.miss == 0
      ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ]
               [ 1 / ethernet.isValid
               , 1 / ethernet.*.init ])
       ) ∧ (
         ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec]
                                       [ 1 / ipv4.isValid
                                       , 1 / ipv4.*.init
                                       , ipv4.srcAddr / meta.ipv4_sa
                                       , 1 / meta.ipv4_sa
                                       , ipv4.dstAddr / meta.ipv4_da
                                       , 1 / meta.ipv4_da.init
                                       , ipv4.totalLen - 20 / meta.tcpLength
                                       , 1 / meta.tcpLength.init ]
                                       [ 1 / ethernet.isValid
                                       , 1 / ethernet.*.init ])
       )
     )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat))))))
  )

) ∧ ethernet.etherType != ETHERTYPE_IPV4 ⇒(
meta.if_index.init == 1
∧
(γ_if_info.meta.if_index == meta.if_index ⇒ (
  ((ρ_if_info.meta.if_index == meta.if_index
   ∧ γ_if_info.miss == 0
   ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
      (ρ_if_info.action == 1 ⇒ 
       (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
             , 1 / meta.if_ipv4_addr.init
             , ρ_if_info.data.mac_addr / meta.if_mac_addr
             , 1 / meta.if_mac_addr.init
             , ρ_if_info.data.is_ext / meta.is_ext_if
             , 1 / meta.is_ext_if.init]
             [ 1 / ethernet.isValid
             , 1 / ethernet.*.init ])
       ) ∧ (
       ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec]
                                     [ 1 / ethernet.isValid
                                     , 1 / ethernet.*.init ])
       ))
   )
  ∧ 
  (γ_if_info.miss == 1 ⇒ ϕ_nat[ 1 / ethernet.isValid
                               , 1 / ethernet.*.init ]))
)))))
```

and we finally get our formula by initializing the init and valid bits to 0

```
ϕ = 
ϕₚ[ 0 / cpu_header.isValid
  , 0 / cpu_header.*.init
  , 0 / ethernet.isValid
  , 0 / ethernet.*.init
  , 0 / ipv4.isValid
  , 0 / ipv4.*.init
  , 0 / tcp.isValid
  , 0 / tcp.*.init
  , 0 / meta.*.init
]
```

## The full formula.

This is still inscrutable, so lets unfold all of the subsitutions and
conditions, and see what we get.



```
pkt.lookahead == 0 ⇒ (
  ((
  ethernet.etherType == ETHERTYPE_IPV4 ⇒
  ((( ipv4.protocol == IP_PROT_TCP ⇒ (
  ((γ_if_info.meta.if_index == cpu_header.if_index  ⇒ (
    ((ρ_if_info.meta.if_index == cpu_header.if_index 
     ∧ γ_if_info.miss == 0
     ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / tcp.isValid
               , 1 / tcp.*.init
               , tcp.srcPort / meta.tcp_sp
               , 1 / meta.tcp_sp.init
               , tcp.dstPort / meta.tcp_dp
               , 1 / meta.tcp_dp.init ]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ]
               [ 1 / cpu_header.*.init
               , pkt.lookahead / cpu_header.preamble
               , cpu_header.if_index / meta.if_index
               , 1 / meta.if_index.init
               , 1 / ethernet.isValid
               , 1 / ethernet.*.init ])
         ) ∧ (
         ρ_if_info.action == 0 ⇒ (
           ϕ_nat[DROP / standard_metadata.egress_spec]
                [ 1 / tcp.isValid 
                , 1 / tcp.*.init
                , tcp.srcPort / meta.tcp_sp
                , 1 / meta.tcp_sp.init
                , tcp.dstPort / meta.tcp_dp
                , 1 / meta.tcp_dp.init ]
                [ 1 / ipv4.isValid
                , 1 / ipv4.*.init
                , ipv4.srcAddr / meta.ipv4_sa
                , 1 / meta.ipv4_sa
                , ipv4.dstAddr / meta.ipv4_da
                , 1 / meta.ipv4_da.init
                , ipv4.totalLen - 20 / meta.tcpLength
                , 1 / meta.tcpLength.init ]
                [ 1 / cpu_header.*.init
                , pkt.lookahead / cpu_header.preamble
                , cpu_header.if_index / meta.if_index
                , 1 / meta.if_index.init
                , 1 / ethernet.isValid
                , 1 / ethernet.*.init ])
         )
    )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat[ 1 / cpu_header.*.init
                                , pkt.lookahead / cpu_header.preamble
                                , cpu_header.if_index / meta.if_index
                                , 1 / meta.if_index.init
                                , 1 / ethernet.isValid
                                , 1 / ethernet.*.init ]))))
)) 
∧ (ipv4.protocol != IP_PROT_TCP ⇒ 
   ((γ_if_info.meta.if_index == cpu_header.if_index ⇒ (
     ((ρ_if_info.meta.if_index == cpu_header.if_index 
      ∧ γ_if_info.miss == 0
      ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ]
               [ 1 / cpu_header.*.init
               , pkt.lookahead / cpu_header.preamble
               , cpu_header.if_index / meta.if_index
               , 1 / meta.if_index.init
               , 1 / ethernet.isValid
               , 1 / ethernet.*.init ])
       ) ∧ (
         ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec]
                                       [ 1 / ipv4.isValid
                                       , 1 / ipv4.*.init
                                       , ipv4.srcAddr / meta.ipv4_sa
                                       , 1 / meta.ipv4_sa
                                       , ipv4.dstAddr / meta.ipv4_da
                                       , 1 / meta.ipv4_da.init
                                       , ipv4.totalLen - 20 / meta.tcpLength
                                       , 1 / meta.tcpLength.init ]
                                       [ 1 / cpu_header.*.init
                                       , pkt.lookahead / cpu_header.preamble
                                       , cpu_header.if_index / meta.if_index
                                       , 1 / meta.if_index.init
                                       , 1 / ethernet.isValid
                                       , 1 / ethernet.*.init ])
       )
     )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat[ 1 / cpu_header.*.init
                                , pkt.lookahead / cpu_header.preamble
                                , cpu_header.if_index / meta.if_index
                                , 1 / meta.if_index.init
                                , 1 / ethernet.isValid
                                , 1 / ethernet.*.init ]))))))
  )

) ∧ ethernet.etherType != ETHERTYPE_IPV4 ⇒(
(γ_if_info.meta.if_index == cpu_header.if_index ⇒ (
  ((ρ_if_info.meta.if_index == cpu_header.if_index 
   ∧ γ_if_info.miss == 0
   ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
      (ρ_if_info.action == 1 ⇒ 
       (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
             , 1 / meta.if_ipv4_addr.init
             , ρ_if_info.data.mac_addr / meta.if_mac_addr
             , 1 / meta.if_mac_addr.init
             , ρ_if_info.data.is_ext / meta.is_ext_if
             , 1 / meta.is_ext_if.init]
             [ 1 / cpu_header.*.init
             , pkt.lookahead / cpu_header.preamble
             , cpu_header.if_index / meta.if_index
             , 1 / meta.if_index.init
             , 1 / ethernet.isValid
             , 1 / ethernet.*.init ])
       ) ∧ (
       ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec]
                                     [ 1 / cpu_header.*.init
                                     , pkt.lookahead / cpu_header.preamble
                                     , cpu_header.if_index / meta.if_index
                                     , 1 / meta.if_index.init
                                     , 1 / ethernet.isValid
                                     , 1 / ethernet.*.init ])
      )
   )
  )
  ∧ 
  (γ_if_info.miss == 1 ⇒ ϕ_nat [ 1 / cpu_header.*.init
                                , pkt.lookahead / cpu_header.preamble
                                , cpu_header.if_index / meta.if_index
                                , 1 / meta.if_index.init
                                , 1 / ethernet.isValid
                                , 1 / ethernet.*.init ])
)))))
∧ pkt.lookahead != 0 ⇒ (
  (ethernet.dstAddr == pkt.lookahead[0:48];
  ∧ ethernet.srcAddr[0:16] == ethernet.srcAddr[0:16])
  ⇒ ((
  ethernet.etherType == ETHERTYPE_IPV4 ⇒
  ((( ipv4.protocol == IP_PROT_TCP ⇒ (
  (meta.if_index.init == 1
  ∧
  (γ_if_info.meta.if_index == meta.if_index ⇒ (
    ((ρ_if_info.meta.if_index == meta.if_index
     ∧ γ_if_info.miss == 0
     ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / tcp.isValid
               , 1 / tcp.*.init
               , tcp.srcPort / meta.tcp_sp
               , 1 / meta.tcp_sp.init
               , tcp.dstPort / meta.tcp_dp
               , 1 / meta.tcp_dp.init ]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ]
               [ 1 / ethernet.isValid
               , 1 / ethernet.*.init ])
         ) ∧ (
         ρ_if_info.action == 0 ⇒ (
           ϕ_nat[DROP / standard_metadata.egress_spec]
                [ 1 / tcp.isValid 
                , 1 / tcp.*.init
                , tcp.srcPort / meta.tcp_sp
                , 1 / meta.tcp_sp.init
                , tcp.dstPort / meta.tcp_dp
                , 1 / meta.tcp_dp.init ]
                [ 1 / ipv4.isValid
                , 1 / ipv4.*.init
                , ipv4.srcAddr / meta.ipv4_sa
                , 1 / meta.ipv4_sa
                , ipv4.dstAddr / meta.ipv4_da
                , 1 / meta.ipv4_da.init
                , ipv4.totalLen - 20 / meta.tcpLength
                , 1 / meta.tcpLength.init ]
                [ 1 / ethernet.isValid
                , 1 / ethernet.*.init ])
         )
    )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat[ 1 / ethernet.isValid, 1 / ethernet.*.init ]))))
)) 
∧ (ipv4.protocol != IP_PROT_TCP ⇒ 
   (meta.if_index.init == 1
   ∧
   (γ_if_info.meta.if_index == meta.if_index ⇒ (
     ((ρ_if_info.meta.if_index == meta.if_index
      ∧ γ_if_info.miss == 0
      ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
        (ρ_if_info.action == 1 ⇒ 
         (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
               , 1 / meta.if_ipv4_addr.init
               , ρ_if_info.data.mac_addr / meta.if_mac_addr
               , 1 / meta.if_mac_addr.init
               , ρ_if_info.data.is_ext / meta.is_ext_if
               , 1 / meta.is_ext_if.init]
               [ 1 / ipv4.isValid
               , 1 / ipv4.*.init
               , ipv4.srcAddr / meta.ipv4_sa
               , 1 / meta.ipv4_sa
               , ipv4.dstAddr / meta.ipv4_da
               , 1 / meta.ipv4_da.init
               , ipv4.totalLen - 20 / meta.tcpLength
               , 1 / meta.tcpLength.init ]
               [ 1 / ethernet.isValid
               , 1 / ethernet.*.init ])
       ) ∧ (
         ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec]
                                       [ 1 / ipv4.isValid
                                       , 1 / ipv4.*.init
                                       , ipv4.srcAddr / meta.ipv4_sa
                                       , 1 / meta.ipv4_sa
                                       , ipv4.dstAddr / meta.ipv4_da
                                       , 1 / meta.ipv4_da.init
                                       , ipv4.totalLen - 20 / meta.tcpLength
                                       , 1 / meta.tcpLength.init ]
                                       [ 1 / ethernet.isValid
                                       , 1 / ethernet.*.init ])
       )
     )
   )
   ∧ 
   (γ_if_info.miss == 1 ⇒ ϕ_nat[ 1 / ethernet.isValid, 1 / ethernet.*.init ]))))))
  )

) ∧ ethernet.etherType != ETHERTYPE_IPV4 ⇒(
meta.if_index.init == 1
∧
(γ_if_info.meta.if_index == meta.if_index ⇒ (
  ((ρ_if_info.meta.if_index == meta.if_index
   ∧ γ_if_info.miss == 0
   ∧ γ_if_info.hitAction == ρ_if_info.id) ⇒ (
      (ρ_if_info.action == 1 ⇒ 
       (ϕ_nat[ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
             , 1 / meta.if_ipv4_addr.init
             , ρ_if_info.data.mac_addr / meta.if_mac_addr
             , 1 / meta.if_mac_addr.init
             , ρ_if_info.data.is_ext / meta.is_ext_if
             , 1 / meta.is_ext_if.init]
             [ 1 / ethernet.isValid
             , 1 / ethernet.*.init ])
       ) ∧ (
       ρ_if_info.action == 0 ⇒(ϕ_nat[DROP / standard_metadata.egress_spec]
                                     [ 1 / ethernet.isValid
                                     , 1 / ethernet.*.init ])
       ))
   )
  ∧ 
  (γ_if_info.miss == 1 ⇒ ϕ_nat[ 1 / ethernet.isValid, 1 / ethernet.*.init ]))
)))))
```


```
substitute 
     [ ρ_if_info.data.ipv4_addr / meta.if_ipv4_addr
     , 1 / meta.if_ipv4_addr.init
     , ρ_if_info.data.mac_addr / meta.if_mac_addr
     , 1 / meta.if_mac_addr.init
     , ρ_if_info.data.is_ext / meta.is_ext_if
     , 1 / meta.is_ext_if.init]
     [ 1 / tcp.isValid
     , 1 / tcp.*.init
     , tcp.srcPort / meta.tcp_sp
     , 1 / meta.tcp_sp.init
     , tcp.dstPort / meta.tcp_dp
     , 1 / meta.tcp_dp.init ]
     [ 1 / ipv4.isValid
     , 1 / ipv4.*.init
     , ipv4.srcAddr / meta.ipv4_sa
     , 1 / meta.ipv4_sa
     , ipv4.dstAddr / meta.ipv4_da
     , 1 / meta.ipv4_da.init
     , ipv4.totalLen - 20 / meta.tcpLength
     , 1 / meta.tcpLength.init ]
     [ 1 / cpu_header.*.init
     , pkt.lookahead / cpu_header.preamble
     , cpu_header.if_index / meta.if_index
     , 1 / meta.if_index.init
     , 1 / ethernet.isValid
     , 1 / ethernet.*.init ]
into
ϕ_nat
===
( γ_nat.meta.is_ext_if = ρ_if_info.data.is_ext
  ∧ γ_nat.meta.ipv4.isValid = ipv4.isValid
  ∧ γ_nat.meta.tcp.isValid = tcp.isValid
  ∧ γ_nat.ipv4.srcAddr = ipv4.srcAddr
  ∧ γ_nat.ipv4.dstAddr = ipv4.dstAddr
  ∧ γ_nat.tcp.srcPort = tcp.srcPort
  ∧ γ_nat.tcp.dstPort = tcp.dstPort
) ⇒ ( 
  ϕ_nat_hit ∧
  ϕ_nat_miss
)
===
( γ_nat.meta.is_ext_if = ρ_if_info.data.is_ext
  ∧ γ_nat.meta.ipv4.isValid = ipv4.isValid
  ∧ γ_nat.meta.tcp.isValid = tcp.isValid
  ∧ γ_nat.ipv4.srcAddr = ipv4.srcAddr
  ∧ γ_nat.ipv4.dstAddr = ipv4.dstAddr
  ∧ γ_nat.tcp.srcPort = tcp.srcPort
  ∧ γ_nat.tcp.dstPort = tcp.dstPort
) ⇒ ( 
ϕ_nat_hit ∧ (
γ_nat.miss == 1 ⇒
meta.do_forward.init == 1 ∧ ipv4.ttl.init == 1 ∧
(meta.do_forward == 1 ∧ ipv4.ttl > 0 ⇒
 γ_ipv4_lpm.meta.ipv4_da = meta.ipv4_da ⇒
   ρ_ipv4_lpm.ipv4_daMask == 0 ⇒ ϕ_ipv4_lpm_inner
   ∧ (ρ_ipv4_lpm.ipv4_daMask != 0 ⇒ 
         (meta.ipv4_da & ρ_ipv4_lpm.ipv4_daMask == ρ_ipv4_lpm.ipv4 & ρ_ipv4_lpm.ipv4_daMask
            ⇒ (γ_ipv4_lpm.miss == 0 ∧ γ_ipv4_lpm.hitAction == ρ_ipv4_lpm.id
                ⇒ ((ρ_ipv4_lpm.action == 0 ⇒ 
                     (ipv4.ttl.init == 1 ∧ 
                      (γ_forward.meta.nhop_ipv4 == ρ_ipv4_lpm.nhop_ivp4  ⇒
                       ((ρ_ipv4_lpm.nhop_ivp4  == ρ_forward.nhop_ipv4
                        ∧ γ_forward.miss == 0
                        ∧ γ_forward.hitAction = ρ_forward.id)
                        ⇒ 
                         (ρ_forward.action == 0 ⇒ 
                           (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                              (ρ_ipv4_lpm.port == γ_send_frame.standard_metadata.egress_port) ⇒
                                ( (ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                  ∧ γ_send_frame.miss == 0
                                  ∧ γ_forward.hitAction = ρ_send_frame.id
                                  ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                ∧ meta.ipv4_da.init == 1 
                                                                ∧ meta.tcp_sp.init == 1
                                                                ∧ meta.tcp_dp.init == 1))))
                             ∧
                             (standard_metadata.instance_type != 0 ⇒
                               (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                          (meta.if_index.init == 1)))))))
                       ∧ (γ_forward.miss == 1 ⇒ (ρ_ipv4_lpm.port != DROP ⇒ (
                             (standard_metadata.instance_type == 0 ⇒
                                (ρ_ipv4_lpm.port  == γ_send_frame.standard_metadata.egress_port) ⇒
                                  ( ( ρ_ipv4_lpm.port == ρ_send_frame.standard_metadata.egress_port
                                    ∧ γ_send_frame.miss == 0
                                    ∧ γ_forward.hitAction = ρ_send_frame.id
                                    ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                                                  ∧ meta.ipv4_da.init == 1 
                                                                  ∧ meta.tcp_sp.init == 1
                                                                  ∧ meta.tcp_dp.init == 1))))
                             ∧ 
                             (standard_metadata.instance_type != 0 ⇒
                                (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
                                  (meta.if_index.init == 1)))))))))
                    ∧ 
                    (ρ_ipv4_lpm.action == 1 ⇒ meta.nhop_ipv4.init == 1 ))))))
∧ ¬ (meta.do_forward == 1 ∧ ipv4.ttl > 0) ⇒ (standard_metadata.egress_spec != DROP ⇒ (
 (standard_metadata.instance_type == 0 ⇒
   (standard_metadata.egress_spec == γ_send_frame.standard_metadata.egress_port) ⇒
      ( (standard_metadata.egress_spec == ρ_send_frame.standard_metadata.egress_port
         ∧ γ_send_frame.miss == 0
         ∧ γ_forward.hitAction = ρ_send_frame.id
         ∧ ρ_send_frame.action = 0 ⇒ (  meta.ipv4_sa.init == 1
                                       ∧ meta.ipv4_da.init == 1 
                                       ∧ meta.tcp_sp.init == 1
                                       ∧ meta.tcp_dp.init == 1))))
  ∧
  standard_metadata.instance_type != 0 ⇒
    (γ_send_frame.miss == 0 ∧ γ_forward.hitAction == ρ_send_frame.id ∧ ρ_send_frame.action == 0 ⇒
       (meta.if_index.init == 1))))))
```


### THIS IS GETTING CHAOTIC

What do we get if we compute the WP automatically and simplify using Z3's
`simplify` command? For simplicity we can remove much of the ghost
instrumentation.

```
(forall ((cpu_header__if_index (_ BitVec 9))
         (ethernet__etherType (_ BitVec 16))
         (ipv4__dstAddr (_ BitVec 32))
         (ipv4__protocol (_ BitVec 8))
         (ipv4__srcAddr (_ BitVec 32))
         (ipv4__ttl (_ BitVec 8))
         (pkt__lookahead (_ BitVec 64))
         (standard_metadata__egress_spec (_ BitVec 9))
         (standard_metadata__ingress_port (_ BitVec 9))
         (standard_metadata__instance_type (_ BitVec 32))
         (tcp__dstPort (_ BitVec 32))
         (tcp__srcPort (_ BitVec 32)))
  (let ((a!1 (and (or (not (= row_send_frame__action #b0))
                      (not (= ghost_send_frame__miss #b0))
                      (not (= row_ipv4_lpm__port
                              row_send_frame__standard_metadata__egress_port))
                      (not (= standard_metadata__instance_type #x00000000))
                      (not (= row_forward__action #b0))
                      (not (= row_ipv4_lpm__port #b111111111)))
                  (or (not (= row_send_frame__action #b0))
                      (not (= ghost_send_frame__miss #b0))
                      (not (= standard_metadata__instance_type #x00000000))
                      (not (= row_forward__action #b0))
                      (not (= row_send_frame__standard_metadata__egress_port
                              #b111111111)))))
        (a!6 (or (not (= row_send_frame__action #b0))
                 (not (= ghost_send_frame__miss #b0))
                 (not (= standard_metadata__instance_type #x00000000))
                 (not (= ipv4__ttl #x00))
                 (not (= standard_metadata__egress_spec
                         row_send_frame__standard_metadata__egress_port))
                 (not (= standard_metadata__egress_spec #b111111111))))
        (a!7 (or (not (= row_send_frame__action #b0))
                 (not (= ghost_send_frame__miss #b0))
                 (not (= standard_metadata__instance_type #x00000000))
                 (not (= standard_metadata__egress_spec
                         row_send_frame__standard_metadata__egress_port))
                 (not (= standard_metadata__egress_spec #b111111111))))
        (a!8 (= (bvnot (bvor (bvnot row_nat__data__dstAddr)
                             (bvnot row_ipv4_lpm__meta_ipv4Mask)))
                (bvnot (bvor (bvnot row_ipv4_lpm__meta_ipv4)
                             (bvnot row_ipv4_lpm__meta_ipv4Mask)))))
        (a!11 (= (bvnot (bvor (bvnot tcp__dstPort) (bvnot row_nat__dstPortMask)))
                 (bvnot (bvor (bvnot row_nat__dstPort)
                              (bvnot row_nat__dstPortMask)))))
        (a!13 (= (bvnot (bvor (bvnot tcp__srcPort)
                              (bvnot row_nat__tcp__srcPortMask)))
                 (bvnot (bvor (bvnot row_nat__tcp__srcPort)
                              (bvnot row_nat__tcp__srcPortMask)))))
        (a!15 (= (bvnot (bvor (bvnot ipv4__dstAddr)
                              (bvnot row_nat__ipv4__dstAddrMask)))
                 (bvnot (bvor (bvnot row_nat__ipv4__dstAddr)
                              (bvnot row_nat__ipv4__dstAddrMask)))))
        (a!17 (= (bvnot (bvor (bvnot ipv4__srcAddr)
                              (bvnot row_nat__ipv4__srcAddrMask)))
                 (bvnot (bvor (bvnot row_nat__ipv4__srcAddr)
                              (bvnot row_nat__ipv4__srcAddrMask)))))
        (a!33 (or (not (= ghost_nat__miss #b0))
                  (not (= row_nat__dstPortMask #x00000000))
                  (and (not (= row_nat__action #b000))
                       (not (= row_nat__action #b001))
                       (not (= row_nat__action #b011))
                       (not (= row_nat__action #b100))
                       (not (= row_nat__action #b101))))))
  (let ((a!2 (and (or a!1
                      (not (= ghost_forward__miss #b0))
                      (not (= row_ipv4_lpm__nhop_ipv4 row_forward__nhop_ipv4)))
                  (or (not (= row_send_frame__action #b0))
                      (not (= ghost_send_frame__miss #b0))
                      (not (= row_ipv4_lpm__port
                              row_send_frame__standard_metadata__egress_port))
                      (not (= standard_metadata__instance_type #x00000000))
                      (not (= row_ipv4_lpm__port #b111111111))
                      (not (= ghost_forward__miss #b1)))))
        (a!9 (and (or (not (= row_ipv4_lpm__action #b1))
                      (not (= ghost_ipv4_lpm__hitAction row_ipv4_lpm__id))
                      (not (= row_ipv4_lpm__meta_ipv4Mask #x00000000))
                      (not (= ghost_ipv4_lpm__miss #b0)))
                  (or (not (= row_ipv4_lpm__action #b1))
                      (not (= ghost_ipv4_lpm__hitAction row_ipv4_lpm__id))
                      (not (= row_ipv4_lpm__meta_ipv4Mask #x00000000))
                      (not (= ghost_ipv4_lpm__miss #b0))
                      (not a!8))
                  (not (= ghost_ipv4_lpm__miss #b1))))
        (a!34 (or (not (= row_nat__tcp__srcPortMask #x00000000))
                  (and a!33 (not (= row_nat__dstPortMask #x00000000))))))
  (let ((a!3 (and (or (not (= row_ipv4_lpm__action #b0)) a!2)
                  (not (= row_ipv4_lpm__action #b1))))
        (a!35 (or (not (= row_nat__ipv4__dstAddrMask #x00000000))
                  (and a!34 (not (= row_nat__tcp__srcPortMask #x00000000))))))
  (let ((a!4 (or a!3
                 (not (= ghost_ipv4_lpm__hitAction row_ipv4_lpm__id))
                 (not (= row_ipv4_lpm__meta_ipv4Mask #x00000000))
                 (not (= ghost_ipv4_lpm__miss #b0))))
        (a!36 (or (not (= row_nat__ipv4__srcAddrMask #x00000000))
                  (and a!35 (not (= row_nat__ipv4__dstAddrMask #x00000000))))))
  (let ((a!5 (or (not (= ipv4__ttl #x00))
                 (and a!4
                      (not (= row_ipv4_lpm__meta_ipv4Mask #x00000000))
                      (not (= ghost_ipv4_lpm__miss #b1)))))
        (a!22 (and a!4
                   (or a!3
                       (not (= ghost_ipv4_lpm__hitAction row_ipv4_lpm__id))
                       (not (= row_ipv4_lpm__meta_ipv4Mask #x00000000))
                       (not (= ghost_ipv4_lpm__miss #b0))
                       (not a!8))
                   (not (= ghost_ipv4_lpm__miss #b1))))
        (a!37 (or (not (= row_nat__tcp__isValid #b0))
                  (and a!36 (not (= row_nat__ipv4__srcAddrMask #x00000000)))
                  (not (= row_nat__ipv4__isValid #b0)))))
  (let ((a!10 (and (not (= row_nat__action #b000))
                   (not (= row_nat__action #b001))
                   (or (not (= row_nat__action #b011)) (and a!5 a!6 a!7))
                   (or (not (= ipv4__ttl #x00))
                       a!9
                       (not (= row_nat__action #b100)))
                   (or (not (= row_nat__action #b101)) (and a!5 a!6 a!7))))
        (a!23 (and (or (not (= ipv4__ttl #x00)) a!22) a!6 a!7))
        (a!38 (or (not (= row_if_info__data__is_ext row_nat__meta__is_ext_if))
                  (not (= row_if_info__action #b1))
                  (and a!37 (not (= ghost_nat__miss #b1))))))
  (let ((a!12 (and (or (not (= ghost_nat__miss #b0))
                       (not (= row_nat__dstPortMask #x00000000))
                       a!10)
                   (or (not (= ghost_nat__miss #b0))
                       (not (= row_nat__dstPortMask #x00000000))
                       (not a!11)
                       a!10)))
        (a!24 (and (not (= row_nat__action #b000))
                   (not (= row_nat__action #b001))
                   (or (not (= row_nat__action #b011)) (and a!5 a!6 a!7))
                   (or (not (= row_nat__action #b100)) a!23)
                   (or (not (= row_nat__action #b101)) (and a!5 a!6 a!7))))
        (a!39 (or (not (= ghost_if_info__miss #b0))
                  (not (= row_if_info__meta__if_index cpu_header__if_index))
                  (and (not (= row_if_info__action #b0)) a!38)))
        (a!45 (or (not (= ghost_if_info__miss #b0))
                  (and (not (= row_if_info__action #b0)) a!38)
                  (not (= row_if_info__meta__if_index
                          standard_metadata__ingress_port)))))
  (let ((a!14 (and (or (not (= row_nat__tcp__srcPortMask #x00000000)) a!12)
                   (or (not (= row_nat__tcp__srcPortMask #x00000000))
                       (not a!13)
                       a!12)))
        (a!25 (and (or (not (= ghost_nat__miss #b0))
                       (not (= row_nat__dstPortMask #x00000000))
                       a!24)
                   (not (= row_nat__dstPortMask #x00000000))))
        (a!40 (or (not (= ethernet__etherType #x0800))
                  (and a!39 (not (= ghost_if_info__miss #b1)))))
        (a!46 (or (not (= ethernet__etherType #x0800))
                  (and a!45 (not (= ghost_if_info__miss #b1))))))
  (let ((a!16 (and (or (not (= row_nat__ipv4__dstAddrMask #x00000000)) a!14)
                   (or (not (= row_nat__ipv4__dstAddrMask #x00000000))
                       (not a!15)
                       a!14)))
        (a!26 (and (or (not (= row_nat__tcp__srcPortMask #x00000000)) a!25)
                   (not (= row_nat__tcp__srcPortMask #x00000000)))))
  (let ((a!18 (and (or (not (= row_nat__ipv4__srcAddrMask #x00000000)) a!16)
                   (or a!16
                       (not (= row_nat__ipv4__srcAddrMask #x00000000))
                       (not a!17))))
        (a!27 (and (or (not (= row_nat__ipv4__dstAddrMask #x00000000)) a!26)
                   (or (not (= row_nat__ipv4__dstAddrMask #x00000000))
                       (not a!15)
                       a!26))))
  (let ((a!19 (and (or a!18
                       (not (= row_nat__tcp__isValid #b1))
                       (not (= row_nat__ipv4__isValid #b1)))
                   (not (= ghost_nat__miss #b1))))
        (a!28 (and (or (not (= row_nat__ipv4__srcAddrMask #x00000000)) a!27)
                   (or (not (= row_nat__ipv4__srcAddrMask #x00000000))
                       (not a!17)
                       a!27))))
  (let ((a!20 (and (not (= row_if_info__action #b0))
                   (or a!19
                       (not (= row_if_info__data__is_ext
                               row_nat__meta__is_ext_if))
                       (not (= row_if_info__action #b1)))))
        (a!29 (and (or (not (= row_nat__ipv4__isValid #b1))
                       a!28
                       (not (= row_nat__tcp__isValid #b0)))
                   (not (= ghost_nat__miss #b1)))))
  (let ((a!21 (and (or a!20
                       (not (= ghost_if_info__miss #b0))
                       (not (= row_if_info__meta__if_index cpu_header__if_index)))
                   (not (= ghost_if_info__miss #b1))))
        (a!30 (and (not (= row_if_info__action #b0))
                   (or (not (= row_if_info__data__is_ext
                               row_nat__meta__is_ext_if))
                       (not (= row_if_info__action #b1))
                       a!29)))
        (a!42 (and (or a!20
                       (not (= ghost_if_info__miss #b0))
                       (not (= row_if_info__meta__if_index
                               standard_metadata__ingress_port)))
                   (not (= ghost_if_info__miss #b1)))))
  (let ((a!31 (and (or (not (= ghost_if_info__miss #b0))
                       (not (= row_if_info__meta__if_index cpu_header__if_index))
                       a!30)
                   (not (= ghost_if_info__miss #b1))))
        (a!43 (and (or (not (= ghost_if_info__miss #b0))
                       a!30
                       (not (= row_if_info__meta__if_index
                               standard_metadata__ingress_port)))
                   (not (= ghost_if_info__miss #b1)))))
  (let ((a!32 (and (or (not (= ipv4__protocol #x06)) a!21)
                   (or (not (= ipv4__protocol #x06)) a!31)))
        (a!44 (and (or (not (= ipv4__protocol #x06)) a!42)
                   (or (not (= ipv4__protocol #x06)) a!43))))
  (let ((a!41 (and (or (not (= ethernet__etherType #x0800)) a!32) a!40))
        (a!47 (and (or (not (= ethernet__etherType #x0800)) a!44) a!46)))
    (and (or a!41 (not (= pkt__lookahead #x0000000000000000)))
         (or (not (= pkt__lookahead #x0000000000000000)) a!47)))))))))))))))))))
                       a!26))))
  (let ((a!19 (and (or a!18
                       (not (= row_nat__tcp__isValid #b1))
                       (not (= row_nat__ipv4__isValid #b1)))
                   (not (= ghost_nat__miss #b1))))
        (a!28 (and (or (not (= row_nat__ipv4__srcAddrMask #x00000000)) a!27)
                   (or (not (= row_nat__ipv4__srcAddrMask #x00000000))
                       (not a!17)
                       a!27))))
  (let ((a!20 (and (not (= row_if_info__action #b0))
                   (or a!19
                       (not (= row_if_info__data__is_ext
                               row_nat__meta__is_ext_if))
                       (not (= row_if_info__action #b1)))))
        (a!29 (and (or (not (= row_nat__ipv4__isValid #b1))
                       a!28
                       (not (= row_nat__tcp__isValid #b0)))
                   (not (= ghost_nat__miss #b1)))))
  (let ((a!21 (and (or a!20
                       (not (= ghost_if_info__miss #b0))
                       (not (= row_if_info__meta__if_index cpu_header__if_index)))
                   (not (= ghost_if_info__miss #b1))))
        (a!30 (and (not (= row_if_info__action #b0))
                   (or (not (= row_if_info__data__is_ext
                               row_nat__meta__is_ext_if))
                       (not (= row_if_info__action #b1))
                       a!29)))
        (a!42 (and (or a!20
                       (not (= ghost_if_info__miss #b0))
                       (not (= row_if_info__meta__if_index
                               standard_metadata__ingress_port)))
                   (not (= ghost_if_info__miss #b1)))))
  (let ((a!31 (and (or (not (= ghost_if_info__miss #b0))
                       (not (= row_if_info__meta__if_index cpu_header__if_index))
                       a!30)
                   (not (= ghost_if_info__miss #b1))))
        (a!43 (and (or (not (= ghost_if_info__miss #b0))
                       a!30
                       (not (= row_if_info__meta__if_index
                               standard_metadata__ingress_port)))
                   (not (= ghost_if_info__miss #b1)))))
  (let ((a!32 (and (or (not (= ipv4__protocol #x06)) a!21)
                   (or (not (= ipv4__protocol #x06)) a!31)))
        (a!44 (and (or (not (= ipv4__protocol #x06)) a!42)
                   (or (not (= ipv4__protocol #x06)) a!43))))
  (let ((a!41 (and (or (not (= ethernet__etherType #x0800)) a!32) a!40))
        (a!47 (and (or (not (= ethernet__etherType #x0800)) a!44) a!46)))
    (and (or a!41 (not (= pkt__lookahead #x0000000000000000)))
         (or (not (= pkt__lookahead #x0000000000000000)) a!47)))))))))))))))))))
```
