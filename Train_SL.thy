header {*The train on-board control system*}

theory Train_SL
imports Inference_SL
begin  

section {*variables and consts*}

consts
vmax :: real (*max velocity*)
T1 :: real (*max duration of first move*)
T2 :: real (*max duration of second move*)
(* max accerleration*)
cmax :: real

(*Constraints for the consts: should be presented in the paper also*)
axiomatization where
cmaxdef[simp]: "cmax > 0" and 
T1def[simp]: "T1 > 0" and
T2def[simp]: "T2 > 0" and
vmaxdef[simp]: "vmax > 0 & vmax > 2*cmax*T1 + 2*cmax*T2" 

(*Continuous variables*)
definition t1 :: "exp" where
"t1 == RVar ''t1''"
definition t2 :: "exp" where
"t2 == RVar ''t2''"
definition s :: "exp" where
"s == RVar ''s''"
definition v :: "exp" where
"v == RVar ''v''"
definition a :: "exp" where
"a == RVar ''a''"

(*Channels*)
definition traind :: string where
"traind = ''traind''"
definition trainv :: string where
"trainv = ''trainv''"
definition driver :: string where
"driver = ''driver''"
definition vc :: string where
"vc = ''vc''"

(*only xa and ya are different in VAx and VAy: should find a unified way to express this*)
(*xa and ya are accelerations received from the driver and vc*)
definition xa :: "exp" where
"xa = RVar ''xa''"
definition ya :: "exp" where
"ya = RVar ''ya''"

definition VAx :: "fform" where
"VAx == ((v [>]Real (vmax - cmax * T1 - cmax * T2)) [\<longrightarrow>] (xa [<] Real 0 [&] xa [\<ge>] Real - cmax)) [&]
       ((v [<] Real (cmax * T1 + cmax*T2)) [\<longrightarrow>] (xa [\<ge>] Real 0 [&] xa [\<le>]  Real cmax))
[&] ((v [\<le>] Real (vmax - cmax * T1 - cmax * T2) [&] v [\<ge>] Real (cmax * T1 + cmax*T2)) [\<longrightarrow>] (xa [\<le>] Real cmax [&] xa [\<ge>] Real - cmax))"

definition VAy :: "fform" where
"VAy == ((v [>]Real (vmax - cmax * T1 - cmax * T2)) [\<longrightarrow>] ((ya [<]  Real 0) [&] (ya [\<ge>]  Real - cmax))) [&]
       ((v [<] Real (cmax * T1 + cmax*T2)) [\<longrightarrow>] ((ya [\<ge>] Real 0) [&] (ya [\<le>]  Real cmax)))
[&] (((v [\<le>]  Real (vmax - cmax * T1 - cmax * T2)) [&] (v [\<ge>]  Real (cmax * T1 + cmax*T2))) [\<longrightarrow>] ((ya [\<le>]  Real cmax) [&] (ya [\<ge>] Real - cmax)))"

section {*binders*}

(*uv, wv, ua, wa: acknowledgement variables*)
definition uv :: "string" where
"uv == ''11''"
definition wv :: "string" where
"wv == ''22''"
definition ua :: "string" where
"ua == ''33''"
definition wa :: "string" where
"wa == ''44''"

(*The only quality predicate: exist*)
definition exist :: "qualityp" where
"exist == % x y. x [|] y"

(*The four binders existing in the train model*)
definition b1 :: "bindp" where
"b1 == & exist [(traind!!v{uv}), (trainv!!v{wv})]"
definition b2 :: "bindp" where
"b2 == & exist [(driver??xa{ua}), (vc??ya{wa})]"
definition b3 :: "bindp" where
"b3 == driver?? xa{ua}"
definition b4 :: "bindp" where
"b4 == vc??ya{wa}"

section {*Processes*}

(*The different invariants for the equations*)
 
section {*Invariants*}
(*The differential invariants for the three continuous evolution in Move1, Move2, and SelfC above. They are strong enough 
to prove the properties as required in the paper. *)
definition Acc1 :: "fform" where
"Acc1 == (a [<] Real 0 [&] ((v [\<ge>] (Real (cmax * T2) [+] (a [*] t1) [+] Real (cmax * T1)) [&] (v [\<le>] Real vmax))))"
definition Acc2 :: "fform" where
"Acc2 == (a [\<ge>] Real 0 [&] ((v [\<le>] ((Real vmax) [+] (a [*] t1)  [+] (Real (-cmax * T2))  [+] Real (-cmax * T1))) [&] (v [\<ge>] Real 0)))"

definition Inv1 :: "fform" where
"Inv1 == ((t1 [\<ge>] (Real 0)) [&] (t1 [\<le>] (Real T1))) [&]
        (Acc1 [|] Acc2)"

definition Acc3 :: "fform" where
"Acc3 ==  (a [<] Real 0 [&] ((v [\<ge>] (Real (cmax * T2) [+] (a [*] t2)) [&] (v [\<le>] Real vmax))))"
definition Acc4 :: "fform" where
"Acc4 ==  (a [\<ge>] Real 0 [&] ((v [\<le>] ((Real vmax) [+] (a [*] t2)  [+] (Real (-cmax * T2)))) [&] (v [\<ge>] Real 0)))"

definition Inv2 :: "fform" where
"Inv2 == ((t2 [\<ge>] (Real 0)) [&] (t2 [\<le>] (Real T2))) [&]
         (Acc3 [|] Acc4)"

definition Inv3 :: "fform" where
"Inv3 ==  (v [\<ge>] Real 0) [&]  (v [\<le>] Real vmax)"

(*Self control by the train*)
definition SelfC :: "bproc" where
"SelfC == a := (Real -cmax);
         <[(''s''), (''v'')]:[v, a]&&Inv3&v[>]Real 0 >;
          a := (Real 0)"


(*When the train fails to send the velocity within T1 time units, then self control.*)
definition P1 :: "bproc" where
"P1 == IF (t1 [\<ge>] Real T1) SelfC"

(*When the train fails to receive the acceleration within T2 time units, then self control.*)
definition P2 :: "bproc" where
"P2 == IF (t2 [\<ge>] Real T2) SelfC"

(*Under Case 1, Case for receiving a from vc successfully*)
definition uvwvwa :: "bproc" where
"uvwvwa == IF (RVar wa [=] Real 1) ((IF VAy (a := ya)); (IF ([\<not>]VAy) SelfC))"

(*Under Case 1, Case for receiving a from driver successfully*)
definition uvwvua :: "bproc" where
"uvwvua == IF ((RVar wa [=] Real 0) [&] (RVar ua [=] Real 1)) ((IF VAx (a := xa)); (IF ([\<not>]VAx) SelfC))"

(*Under Case 1, Case for failing to receive from both*)
definition uvwvnon :: "bproc" where
"uvwvnon == IF (([\<not>](RVar wa [=] Real 1)) [&] ([\<not>]((RVar wa [=] Real 0) [&] (RVar ua [=] Real 1))) ) Skip"
 
definition Quvwv :: "bproc" where
"Quvwv == uvwvwa; uvwvua; uvwvnon "

(*Under Case 1, the train waits for receiving a from vc and driver*)
definition move2 :: "bproc" where
"move2 == <[(''s''), (''v''), (''t2'')]:[v, a, Real 1]&&Inv2& (t2 [<] (Real T2))>[[ b2  Quvwv"


(*Under Case 2, Case for receiving a from driver *)        
definition uvua :: "bproc" where
"uvua ==  IF ((RVar ua [=] Real 1)) ((IF VAx (a := xa)); (IF ([\<not>]VAx) SelfC))"

(*Under Case 2, Case for failing to receive a from driver *)        
definition uvnon :: "bproc" where
"uvnon ==  IF ([\<not>](RVar ua [=] Real 1)) Skip"

definition Quv :: "bproc" where
"Quv ==  uvua; uvnon"

(*Under Case 2, the train waits for receiving a from driver*)
definition move3 :: "bproc" where
"move3 == <[(''s''), (''v''), (''t2'')]:[v, a, Real 1]&&Inv2& (t2 [<] (Real T2))>[[ b3  Quv"

(*Case 2: the train sends the velocity successfully to driver while not vc.*)
definition Cuv :: "bproc" where
"Cuv == t2 := (Real 0); move3"

(*Under Case 3, Case for receiving a from vc *)        
definition wvwa :: "bproc" where
"wvwa ==  IF ((RVar wa [=] Real 1)) ((IF VAy (a := ya)); (IF ([\<not>]VAy) SelfC))"

(*Under Case 3, Case for failing to receive a from vc *)        
definition wvnon :: "bproc" where
"wvnon == IF ([\<not>](RVar wa [=] Real 1)) Skip"

definition Qwv :: "bproc" where
"Qwv ==   wvwa; wvnon"

definition move4 :: "bproc" where
"move4 ==  <[(''s''), (''v''), (''t2'')]:[v, a, Real 1]&&Inv2& (t2 [<] (Real T2))>[[ b4  Qwv"

(*Case 3: the train sends the velocity successfully to vc while not driver.*)
definition Cwv :: "bproc" where
"Cwv == t2 := (Real 0); move4"

definition case1 :: "bproc" where
"case1 == (IF  ((RVar uv [=] Real 1) [&] (RVar wv [=] Real 1)) (t2 := (Real 0); move2; P2))"
definition case2 :: "bproc" where
"case2 == (IF  ((RVar uv [=] Real 1) [&] (RVar wv [=] Real 0)) (Cuv; P2))"
definition case3 :: "bproc" where
"case3 == (IF  ((RVar uv [=] Real 0) [&] (RVar wv [=] Real 1)) (Cwv; P2))"
definition case4 :: "bproc" where
"case4 == (IF ( ([\<not>]((RVar uv [=] Real 1) [&] (RVar wv [=] Real 1)))
[&] ([\<not>]((RVar uv [=] Real 1) [&] (RVar wv [=] Real 0)))
[&] ([\<not>]((RVar uv [=] Real 0) [&] (RVar wv [=] Real 1)))
)
 Skip)"

(*The train sends v and asks for a from vc and driver, the body command*)
definition body :: "bproc" where
"body == <[(''s''), (''v''), (''t1'')]:[v, a, Real 1]&&Inv1& (t1 [<] (Real T1))>[[
                       b1 (case1; case2; case3; case4)"
definition train :: "bproc" where
"train ==  t1:= (Real 0); body; P1"

declare t1_def [simp]
declare t2_def [simp]
declare s_def [simp]
declare v_def [simp]
declare a_def [simp] 

end