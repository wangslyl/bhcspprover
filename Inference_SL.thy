header {*The Inference System based on first-order logic for bHCSP;
         Prover II
      *}

theory Inference_SL
  imports bSyntax_SL
begin

consts 
spec :: "fform \<Rightarrow> bproc => fform => fform => prop"   ("{_}_{_;_}" 80)

section {*Acknowledgement judgement for binders*}
primrec bAck :: "bindp => fform" 
where
"bAck(ch??x{u}) = ((RVar u) [=]Real 1)" |
"bAck(ch!!e{u}) = ((RVar u) [=]Real 1)"|
"bAck(&q [b, d]) = (q (bAck(b)) (bAck(d)))"
 

(*Consequence rule*)
axiomatization where 
ConsequenceRule : "{ax} P  {qx; Hx} \<Longrightarrow> \<forall> s. ((a [\<longrightarrow>] ax) [&] (qx [\<longrightarrow>] q) [&] (Hx [\<longrightarrow>] H)) s
              ==> {a} P  {q; H}"
(*Skip rule*)
axiomatization where
Skip : "\<forall> s. (( p [\<longrightarrow>] q)  [&] (fFalse [\<longrightarrow>] h)) s ==> {p} Skip {q; h}"

(*Assignment rule*)
axiomatization where
AssignRuleR  :"(\<forall> s. p s \<longrightarrow> (q (%y. if (y=x) then (evalE f s) else s y)))
                   \<and> (\<forall> s. (fFalse [\<longrightarrow>] H) s) ==>
       {p} ((RVar x) := f) {q; H}"
 


axiomatization where
InputRuleR : "(([\<exists>] x([\<exists>] u p) [&]((RVar u) [=] Real 1) [\<longrightarrow>] q) [&] ( p [\<longrightarrow>] h)) s ==>
          {p} Qb ch??(RVar x){u} {q; h}"
 

axiomatization where
OutputRule : "((([\<exists>] u p) [&]((RVar u) [=] Real 1) [\<longrightarrow>] q) [&] ( p [\<longrightarrow>] h)) s ==>
          {p} Qb ch!!e{u} {q; h}"


axiomatization where
BinderRule : "\<forall> s. ((Lex p mvarB(&r [b, d]) [&] bAck((&r [b, d]))) [\<longrightarrow>] q)  s
\<Longrightarrow> \<forall> s. (Lex p mvarB(&r [b, d]) [\<longrightarrow>] h) s
          \<Longrightarrow> {p}Qb (&r [b, d]) {q; h}"

axiomatization where
ContinuousRule : "\<forall>s . (Lex p v [&] (close([\<not>]D)[&] close(Inv)) [\<longrightarrow>] q) s \<Longrightarrow> \<forall>s. ((Lex p v [&] D[&]Inv) [\<longrightarrow>] h) s  ==>
              {p} <v:E &&Inv&D> {q; h}"

 
axiomatization where
InterruptRule :  "{Lex ((Lex p v) [&] close(Inv)) mvarB(b) [&] bAck(b)} P {qx; hx} \<Longrightarrow>
\<forall> s. (((Lex ((Lex p v) [&] close(Inv) [&] close([\<not>]D)) mvarB(b) [|] qx) [\<longrightarrow>] q)
[&] ((Lex ((Lex p v) [&] Inv [&]D) mvarB(b)) [|] hx) [\<longrightarrow>] h) s
==> {p} <v:E &&Inv&D>[[b P {q; h}"
 

axiomatization where
ParallelRule : "{p} P {qx; hx} \<Longrightarrow> {p} Q {qy; hy} \<Longrightarrow> \<forall> s. ((qx [&] qy) [\<longrightarrow>] q) s 
        \<Longrightarrow> \<forall> s. ((hx [&] hy) [\<longrightarrow>] h) s
           ==> {p} P || Q {q; h}"


axiomatization where
SequentialRule : "{p} P {qx; hx} \<Longrightarrow> {qx} Q {q; hy}
        \<Longrightarrow> \<forall> s. ((((hx [|] hy) [\<longrightarrow>] h))) s
           ==> {p} P; Q {q; h}"



axiomatization where
IFRule : "{p [&] b} P {qx; h} \<Longrightarrow>\<forall> s. ((((p [&] ([\<not>] b)) [|] qx) [\<longrightarrow>] q) ) s
       \<Longrightarrow>  {p} IF b P {q; h}"
 

axiomatization where
RepetitionRule : " {Inv} P {Inv; h} \<Longrightarrow> \<forall> s. (Inv [\<longrightarrow>] (q)) s \<Longrightarrow> \<forall> s. (p [\<longrightarrow>] (Inv)) s \<Longrightarrow>
              {p} P*&&Inv {q; h}"

  

axiomatization where
ChoiceRule : "{p [&] b} P {q; h}==>
          {p} NON tpid s : b P {q; h}"
end