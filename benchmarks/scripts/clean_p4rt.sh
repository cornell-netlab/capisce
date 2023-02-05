#! /bin/bash


cat ${1} | \
    grep -e "table_entry\|action_profile_member" | \
    sed -e "s/.*entity { //" |\
    sed -e "s/table_entry/TableEntry/g" |\
    sed -e "s/:/ =/g" |\
    sed -e 's/\([[:alnum:]]\) value/\1; value/g' |\
    sed -e 's/\([[:digit:]]\) match /\1; matches = [/g' |\
    sed -e "s/} match {/} ; {/g" |\
    sed -e "s/ exact/; match_key = Exact/g" |\
    sed -e "s/ ternary/; match_key = Ternary/g" | \
    sed -e "s/ lpm/; match_key = Ternary/g" | \
    sed -e "s/ mask =/; mask =/g" | \
    sed -e "s/ prefix_len =/; prefix_len =/g" | \
    sed -e "s/prefix_len = 24/ mask = \"\\\377\\\377\\\377\\\000\"/g" | \
    sed -e "s/} action { action/}]; action = Action/g" | \
    sed -e "s/param/arg/g" | \
    sed -e "s/\([[:digit:]]\) args/\1; args = [/g" | \
    sed -e "s/} args {/}; {/g" | \
    sed -e "s/} } priority/] }; priority/g" | \
    sed -e "s/action_profile_member/ActionProfileMember/g" | \
    sed -e "s/\([[:digit:]]\) member_id/\1;member_id/g" | \
    sed -e "s/action = Action_profile_group_id = /action = Profile { action_profile_member_id = /g" | \
    sed -e "s/\([[:digit:]]\) action { action_id/\1; action_id/g" | \
    sed -e "s/{\( action_id = [[:digit:]]*\) }/{\1; args = []}/g" | \
    sed -e 's/\"\(\\\000\)*\\\00\([[:digit:]]\)\"/Bigint.of_int \2/g' | \
    sed -e 's/\"\(\\\000\)*\\\021\"/ Bigint.of_int 17/g' | \
    sed -e 's/\"\(\\\000\)*\\n\"/Bigint.of_int 10/g' | \
    sed -e 's/\"\\\010\\\000\"/Bigint.of_int 2048/g' | \
    sed -e 's/\"\\\010\\\006\"/Bigint.of_int 2054/g' | \
    sed -e 's/\"\\\017\\376\"/Bigint.of_int 4094/g' | \
    sed -e 's/\"\\\017\\377\"/Bigint.of_int 4095/g' | \
    sed -e 's/\"\\\023\\304\"/Bigint.of_int 5060/g' | \
    sed -e 's/\"\\\023\\305\"/Bigint.of_int 5061/g' | \
    sed -e 's/\"\(\\\000\)*\\\000c\"/ Bigint.of_int 99/g' | \
    sed -e 's/\"\(\\\000\)*\\\000d\"/ Bigint.of_int 100/g' | \
    sed -e 's/\"\(\\\000\)*\\310\"/ Bigint.of_int 200/g' | \
    sed -e 's/\"\(\\\000\)*\\\001,\"/ Bigint.of_int 300/g' | \
    sed -e 's/\"\(\\\000\)*\\\001\\221\"/ Bigint.of_int 401/g' | \
    sed -e 's/\"\(\\\000\)*\\\001\\220\"/ Bigint.of_int 400/g' | \
    sed -e 's/\"\(\\\000\)*\\252\\\001\"/ Bigint.of_int 43521/g' | \
    sed -e 's/\"\(\\\000\)*\\210G\"/ Bigint.of_int 8931116/g' | \
    sed -e 's/\"\(\\\000\)*\\n\\\000\\\001\\\001\"/ Bigint.of_int 167772417/g' | \
    sed -e 's/\"\(\\\000\)*\\n\\\000\\\002\\\000\"/ Bigint.of_int 167772672/g' | \
    sed -e 's/\"\(\\\000\)*\\n\\\000\\\002\\\001\"/ Bigint.of_int 167772673/g' | \
    sed -e 's/\"\(\\\000\)*\\n\\\000\\\003\\\001\"/ Bigint.of_int 167772929/g' | \
    sed -e 's/\"\(\\\000\)*\\n\\\000\\\004\\\000\"/ Bigint.of_int 167773184/g' | \
    sed -e 's/\"\(\\\000\)*\\n\\\000\\\004\\\001\"/ Bigint.of_int 167773185/g' | \
    sed -e 's/\"\(\\\000\)*\\377\"/Bigint.of_int 255/g' | \
    sed -e 's/\"\\377\\377\"/Bigint.of_int 65535/g' | \
    sed -e 's/\"\\377\\377\\377\\377\"/Bigint.of_int 4294967295 /g' | \
    sed -e 's/\"\\377\\377\\377\\\000\"/Bigint.of_int 4294967040 /g' | \
    sed -e 's/\"\\377\\377\\377\\377\\377\\377\"/Bigint.of_string \"281474976710655\" /g' | \
    sed -e 's/priority = 10 } };/priority = 10 };/g' | \
    sed -e 's/\[\]} } } };/\[\]}; priority = -1};/g' | \
    sed -e 's/} } } }/} ] }/g' | \
    sed -e 's/} } } /}; priority = -1}/g' | \
    sed -e 's/} } };/}; priority = -1};/g' | \
    sed -e 's/} ] } };/} ] }; priority = -1};/g' | \
    sed -e "s/;/;\n/g"
