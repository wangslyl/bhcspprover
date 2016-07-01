header {*The proof of the train on-board control system in Prover II*}
theory TrainProof_SL
imports Train_SL
begin
(*Precondition Pre: three conjuncts VA and Vinv and Ain*)
(*Constraints for v and a*)
definition VA :: "fform" where
"VA == ((v [>] Real (vmax - cmax * T1 - cmax * T2)) [\<longrightarrow>] (a [<] Real 0)) [&]
       ((v [<] Real (cmax * T1 + cmax*T2)) [\<longrightarrow>] (a [\<ge>] Real 0))"

definition Vinv :: "fform" where
"Vinv == (v [\<ge>] Real 0) [&] (v [\<le>] Real vmax)"

definition Ainv :: "fform" where
"Ainv == (a [\<le>] Real cmax) [&] (a [\<ge>] Real -cmax)"

definition Pre :: "fform" where
"Pre == VA [&] Vinv [&] Ainv"

section {*Proof*}

definition mid1 :: "fform" where
"mid1 == ((t1 [<] Real T1 [\<longrightarrow>] VA) [|] (t1 [\<ge>] Real T1)) [&] Vinv [&] Ainv"

definition mid11 :: "fform" where
"mid11 == (Lex ([\<exists>] (''s'') [\<exists>] ( ''v'') [\<exists>](''t1'') Pre [&] t1 [=] Real 0) [&] (t1 [\<ge>] Real T1) [&] close(Inv1) mvarB b1)"

definition mid22 :: "fform" where
"mid22 ==  Lex ([\<exists>] (''s'') [\<exists>] ( ''v'') [\<exists>](''t1'') Pre [&] t1 [=] Real 0) [&]
                    t1 [<] Real T1 [&] Inv1 mvarB b1"

lemma mid11fact2 : "\<forall> s. (Ainv [&] (t1 [\<ge>] Real T1) [&] close(Inv1) [\<longrightarrow>] Vinv) s"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv1_def Acc1_def Acc2_def)
apply (simp add:fImp_def fAnd_def fGreaterEqual_def fLessEqual_def fLess_def fOr_def, auto)
apply (smt T2def mult_minus_left mult_right_mono)
by (smt T2def cmaxdef mult_le_0_iff mult_right_mono)

lemma mid11fact : "\<forall> s. (mid11 [\<longrightarrow>] (Ainv [&] (t1 [\<ge>] Real T1) [&] close(Inv1))) s"
apply (simp add:mid11_def Inv1_def Acc1_def Acc2_def)
apply (simp add:b1_def Pre_def uv_def wv_def VA_def Vinv_def Ainv_def Inv1_def Acc1_def Acc2_def fEx_def fAnd_def fLessEqual_def fLess_def fGreater_def  fGreaterEqual_def fOr_def fImp_def fEqual_def)
by metis

lemma mid22fact2 : "\<forall> s. (Ainv [&] (t1 [<] Real T1) [&] Inv1 [\<longrightarrow>] Vinv) s"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv1_def Acc1_def Acc2_def)
apply (simp add:fImp_def fAnd_def fGreaterEqual_def fLessEqual_def fLess_def fOr_def, auto)
apply (smt T2def mult_minus_left mult_mono)
by (smt T2def cmaxdef mult_mono mult_pos_pos)
 
lemma mid22fact : "\<forall> s. (mid22 [\<longrightarrow>](Ainv [&] t1[<]Real T1 [&] Inv1)) s"
apply (simp add:mid22_def b1_def Pre_def uv_def wv_def VA_def Vinv_def Ainv_def Inv1_def Acc1_def Acc2_def fEx_def fAnd_def fLessEqual_def fLess_def fGreater_def  fGreaterEqual_def fOr_def fImp_def fEqual_def)
by metis

lemma mid22fact3 : "\<forall> s. (mid22 [\<longrightarrow>] Vinv) s"
apply (cut_tac mid22fact mid22fact2)
by (metis fImp_def)

lemma mid11fact3 : "\<forall> s. (mid11 [\<longrightarrow>] Vinv) s"
apply (cut_tac mid11fact mid11fact2)
by (metis fImp_def)

lemma mid1fact : "\<forall> s. ((mid11 [|] Pre) [\<longrightarrow>] mid1) s"
apply (simp add:mid1_def fOr_def fImp_def) 
apply (simp add:Pre_def fAnd_def)
apply (cut_tac mid11fact3 mid11fact)
apply (simp add:fImp_def fAnd_def)
done
 
definition afterb1 :: "fform" where
"afterb1 == Lex ([\<exists>] ''s'' [\<exists>] ''v'' [\<exists>] ''t1'' Pre [&] t1 [=] Real 0) [&] close(Inv1) mvarB b1 [&]
                    bAck(b1)"

definition case1B :: "fform" where
"case1B == (RVar uv [=] Real 1 [&] RVar wv [=] Real 1)"

definition mid2 :: "fform" where
"mid2 == ((t2 [<] Real T2 [\<longrightarrow>] VA) [|] (t2 [\<ge>] Real T2)) [&] Vinv [&] Ainv [&] case1B"

definition mid211 :: "fform" where
"mid211 ==  Lex ([\<exists>] ''s'' [\<exists>] ''v'' [\<exists>] ''t2'' afterb1 [&] case1B [&] t2 [=] Real 0) [&]
            (t2 [>] Real T2 [|] t2 [=] Real T2) [&] close(Inv2) mvarB b2"

definition mid212 :: "fform" where
"mid212 == Lex ([\<exists>] ''s'' [\<exists>] ''v'' [\<exists>] ''t2'' afterb1 [&] case1B [&] t2 [=] Real 0) [&]
                t2 [<] Real T2 [&] Inv2 mvarB b2"

lemma mid211fact : "\<forall> s. (mid211 [\<longrightarrow>] (Ainv [&] (t2 [>] Real T2 [|] t2 [=] Real T2) [&] close(Inv2))) s"
apply (simp add:mid211_def b2_def xa_def ua_def ya_def wa_def fEx_def fAnd_def fOr_def fGreater_def fEqual_def fImp_def)
apply (simp add: Inv2_def Acc3_def Acc4_def)
apply (simp add:afterb1_def fEx_def b1_def fAnd_def Pre_def Ainv_def fLessEqual_def fGreaterEqual_def fOr_def fEqual_def)
apply clarsimp
apply (simp add:uv_def wv_def)
by metis

definition BreakPre :: "fform" where
"BreakPre == Lex ([\<exists>] ''s''[\<exists>] ''v'' [\<exists>] ''t2'' afterb1 [&] case1B [&] t2 [=] Real 0) [&]
         close(Inv2) mvarB b2 [&] bAck(b2)"

lemma Break211fact : "\<forall> s. (BreakPre [\<longrightarrow>] (Ainv [&] close(Inv2))) s"
apply (simp add:BreakPre_def b2_def xa_def ua_def ya_def wa_def fEx_def fAnd_def fOr_def fGreater_def fEqual_def fImp_def)
apply (simp add: Inv2_def Acc3_def Acc4_def)
apply (simp add:afterb1_def fEx_def b1_def fAnd_def Pre_def Ainv_def fLessEqual_def fGreaterEqual_def fOr_def fEqual_def)
apply clarsimp
apply (simp add:uv_def wv_def)
by metis

lemma mid211fact2 : "\<forall> s. ((Ainv [&] t2 [\<ge>] Real T2 [&] close(Inv2)) [\<longrightarrow>] Vinv) s"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv2_def Acc3_def Acc4_def)
apply (simp add: fImp_def)
apply (simp add:fAnd_def fGreaterEqual_def fLessEqual_def fOr_def, auto)
using mult_right_mono apply fastforce
by (smt mult_right_mono)

lemma Break211fact2 : "\<forall> s. ((Ainv [&] close(Inv2)) [\<longrightarrow>] Vinv) s"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv2_def Acc3_def Acc4_def)
apply (simp add: fImp_def)
apply (simp add:fAnd_def fGreaterEqual_def fLessEqual_def fOr_def, auto)
apply (smt mult_minus_left mult_mono')
using mult_mono' by fastforce
 
lemma mid211fact3 : "\<forall> s. (mid211 [\<longrightarrow>] Vinv) s"
apply (cut_tac mid211fact mid211fact2)
apply (simp add:fImp_def fAnd_def fGreaterEqual_def fOr_def fGreater_def fEqual_def, auto)
done
 
definition case11B :: "fform" where
"case11B == RVar wa [=] Real 1"

lemma Breakfact11 : "\<forall> s. (BreakPre [\<longrightarrow>] Vinv) s"
apply (cut_tac Break211fact Break211fact2)
apply (simp add:fImp_def)
done

lemma mid212fact31 : "\<forall> s. (mid212 [\<longrightarrow>] Ainv [&] t2 [<] Real T2 [&] Inv2) s"
apply (simp add:mid212_def b2_def xa_def ua_def ya_def wa_def fEx_def fAnd_def fOr_def fGreater_def fEqual_def fImp_def)
apply (simp add: Inv2_def Acc3_def Acc4_def)
apply (simp add:afterb1_def fEx_def b1_def fAnd_def Pre_def Ainv_def fLess_def fLessEqual_def fGreaterEqual_def fOr_def fEqual_def uv_def wv_def)
apply clarsimp
done 

lemma mid212fact32: "\<forall> s. (Ainv [&] t2 [<] Real T2 [&] Inv2 [\<longrightarrow>] Vinv) s"
apply (simp add:Vinv_def Ainv_def)
apply (simp add:Inv2_def Acc3_def Acc4_def)
apply (simp add: fImp_def)
apply (simp add:fAnd_def fGreaterEqual_def fLessEqual_def fOr_def fLess_def, auto)
apply (smt mult_minus_left mult_mono')
by (smt mult_mono')

lemma mid212fact3 : "\<forall> s. (mid212 [\<longrightarrow>] Vinv) s"
apply (cut_tac mid212fact31  mid212fact32)
apply (simp add:fImp_def)
done
 
lemma mid2fact1   : "\<forall> s. (mid211 [\<longrightarrow>] case1B) s"
apply (simp add: mid211_def case1B_def)
apply (simp add:b2_def xa_def ua_def ya_def wa_def uv_def wv_def fEx_def, auto)
apply (simp add:fImp_def)
apply (simp add:fAnd_def fEqual_def, auto)
done

lemma mid2fact : "\<forall> s. ((mid211 [|] (Pre [&] case1B)) [\<longrightarrow>] mid2) s "
apply (simp add:mid2_def)
apply (cut_tac mid211fact3  mid211fact)
apply (simp add:fImp_def fOr_def fAnd_def fLess_def fGreaterEqual_def)
apply (simp add:Pre_def fAnd_def)
apply (cut_tac mid211fact)
apply (simp add:fGreater_def fEqual_def, auto)
apply (cut_tac mid2fact1)
apply (simp add:fImp_def)
done 

lemma VAyfact1 : "{(BreakPre [&] RVar wa [=] Real 1) [&]
     VAy}a := ya{Pre [&] case1B [&] case11B [&] VAy; Vinv}"
apply (simp add:a_def)
apply (rule AssignRuleR)
apply (cut_tac Breakfact11)
apply (simp add:fImp_def Pre_def case11B_def Vinv_def VAy_def ya_def)
apply (simp add:fAnd_def fGreaterEqual_def fLessEqual_def wa_def fEqual_def)
apply (simp add: case1B_def case11B_def BreakPre_def b2_def fLess_def fGreater_def, clarsimp)
apply (simp add:VA_def Ainv_def xa_def ya_def ua_def wa_def fEx_def fAnd_def fEqual_def uv_def wv_def)
apply (simp add:fImp_def fGreaterEqual_def fGreater_def fLessEqual_def fLess_def ya_def)
apply (subgoal_tac "cmax >0 \<and> T1 >0 \<and> T2 >0", auto)
done  

lemma VAyfact : "{BreakPre [&] RVar wa [=] Real 1}
                     IF VAy a := ya{(BreakPre [&] case11B [&] [\<not>] VAy) [|]
                              (Pre [&] case1B [&] case11B [&] VAy); Vinv}"
apply (cut_tac VAyfact1)
apply (cut_tac qx = "Pre [&] case1B [&] case11B [&] VAy" in IFRule, auto)
apply (simp add:case11B_def) 
apply (simp add:fImp_def)
done

lemma Assignfact1 : "{BreakPre [&]
     case11B}a := (Real - cmax){Vinv [&] case1B [&] case11B; Vinv}"
apply (simp add:a_def)
apply (rule AssignRuleR)
apply (cut_tac Breakfact11)
apply (simp add:fImp_def Pre_def case11B_def Vinv_def VAy_def ya_def)
apply (simp add:fAnd_def fGreaterEqual_def fLessEqual_def wa_def fEqual_def)
apply (simp add: case1B_def case11B_def BreakPre_def b2_def fLess_def fGreater_def, clarsimp)
apply (simp add:VA_def Ainv_def xa_def ya_def ua_def wa_def fEx_def fAnd_def fEqual_def uv_def wv_def)
by metis

lemma Breakfact1 : "{Vinv [&] case1B [&] case11B}
<[(''s''), (''v'')]:[v, a]&&Inv3&v[>]Real 0 > {v [=] Real 0 [&] case1B [&] case11B; Vinv}"
apply (rule ContinuousRule, auto)
apply (simp add:Inv3_def)
apply (subgoal_tac "[\<not>]RVar ''v''[>]Real 0 = RVar ''v''[\<le>]Real 0", auto)
apply (simp add:case1B_def case11B_def fAnd_def fEx_def fImp_def fLessEqual_def fGreaterEqual_def fEqual_def
uv_def wv_def ua_def wa_def)
apply (simp add:fNot_def fLessEqual_def fGreater_def)
apply (metis not_less)
apply (simp add:Inv3_def Vinv_def fImp_def fAnd_def)
done   

lemma SelfCfact2 : "{BreakPre [&] case11B} SelfC {Pre [&] case1B [&] case11B; Vinv}"
apply (simp add:SelfC_def)
apply (cut_tac qx = "Vinv [&] case1B [&] case11B" and hx = "Vinv" and hy = "Vinv" in SequentialRule, auto)
apply (cut_tac Assignfact1, auto)
apply (cut_tac qx = "v [=] Real 0 [&] case1B [&] case11B" and hx = "Vinv" and hy = "Vinv" in SequentialRule, auto)
apply (cut_tac Breakfact1, auto)
apply (rule AssignRuleR)
apply (simp add:fImp_def Pre_def VA_def Vinv_def Ainv_def case11B_def case1B_def)
apply (simp add:fAnd_def fEqual_def fLess_def fGreater_def fLessEqual_def fGreaterEqual_def wa_def uv_def wv_def)
using cmaxdef vmaxdef apply linarith
apply (simp add:fImp_def fOr_def)+
done 

lemma NVAyfact : "{(BreakPre [&] case11B [&] ([\<not>] VAy)) [|] (Pre [&] case1B [&]
     case11B [&] VAy)}IF ([\<not>] VAy) SelfC {Pre [&] case1B [&] case11B; Vinv}"
apply (cut_tac qx = "Pre [&] case1B [&] case11B"  in IFRule, auto)
apply (cut_tac ax = "BreakPre [&] case11B" and qx = "Pre [&] case1B [&] case11B" and Hx = "Vinv" in ConsequenceRule, auto)
apply (cut_tac SelfCfact2, auto) 
apply (simp add:fAnd_def fImp_def)
apply (simp add:fImp_def fAnd_def fOr_def fNot_def)
apply metis
apply (simp add:fImp_def fAnd_def fOr_def fNot_def) apply metis
done

lemma uvwvwafact : "{BreakPre}uvwvwa{(BreakPre [&] [\<not>] case11B) [|]
                     (Pre [&] case1B [&] case11B); Vinv}"
apply (simp add:uvwvwa_def)
apply (cut_tac qx = "Pre [&] case1B [&] case11B"  in IFRule, auto)
apply (cut_tac qx = "(BreakPre [&] case11B [&] [\<not>]VAy) [|] (Pre [&] case1B [&] case11B [&] VAy)" and hx = " Vinv"  and hy = " Vinv" in SequentialRule, auto)
apply (cut_tac VAyfact, auto)
apply (cut_tac NVAyfact, auto)
apply (simp add:fImp_def fOr_def)
apply (simp add:case11B_def fImp_def)
done 

definition case12B :: "fform" where
"case12B == (RVar wa [=] Real 0) [&] (RVar ua [=] Real 1)"
definition case13B :: "fform" where
"case13B == ([\<not>](RVar wa [=] Real 1)) [&] ([\<not>]((RVar wa [=] Real 0) [&] (RVar ua [=] Real 1)))"

(*Notice that we define the following facts for processes uvwvua and uvwvnon as axioms rather than proving them as we do to process uvwvwa above. The reason is that they have very similar structure with uvwvwa, and the proofs are almost the same as uvwvwa.*)
axiomatization where
uvwvuafact : "{(BreakPre [&] ([\<not>] case11B)) [|] (Pre [&] case1B [&] case11B)}uvwvua
   {(BreakPre [&]  ([\<not>] case11B) [&]  ([\<not>] case12B)) [|] (Pre [&] case1B [&] (case11B [|] case12B)); Vinv}" and
(*The following fact implies that location 2 is not reachable: the precondition of "uvwvnonfact" in conjunction with the condition in "uvwvnon" are not satisfiable.*)
uvwvnonfact: "{(BreakPre [&]  ([\<not>] case11B) [&]  [\<not>] case12B) [|] (Pre [&] case1B [&] (case11B [|] case12B))}uvwvnon
  {(BreakPre [&]  ([\<not>] case11B) [&]  ([\<not>] case12B) [&]  [\<not>] case13B) [|] (Pre [&] case1B [&] (case11B [|] case12B [|] case13B)); Vinv}"

lemma uanonfact : "{(BreakPre [&]  [\<not>] case11B) [|] (Pre [&] case1B [&] case11B)}uvwvua; uvwvnon{Pre [&] case1B;  Vinv}"
apply (cut_tac qx = "(BreakPre [&]  ([\<not>] case11B) [&]  [\<not>] case12B) [|] (Pre [&] case1B [&] (case11B [|] case12B))" 
and hx = " (Vinv)" and  hy = " (Vinv)" in SequentialRule, auto)
apply (rule uvwvuafact)
apply (cut_tac ax = "(BreakPre [&]  ([\<not>] case11B) [&]  [\<not>] case12B) [|] (Pre [&] case1B [&] (case11B [|] case12B))" 
and qx ="(BreakPre [&]  ([\<not>] case11B) [&]  ([\<not>] case12B) [&]  [\<not>] case13B) [|] (Pre [&] case1B [&] (case11B [|] case12B [|] case13B))" 
 and Hx = " Vinv" in ConsequenceRule, auto)
apply (rule uvwvnonfact)
apply (simp add:fImp_def fAnd_def fOr_def fNot_def)
apply (simp add:case11B_def case12B_def case13B_def fAnd_def fEqual_def fNot_def)
apply metis
apply (simp add:fOr_def fImp_def)
done 

lemma Break1body : "{BreakPre}uvwvwa; uvwvua; uvwvnon{Pre [&] case1B; Vinv}"
apply (cut_tac qx = "(BreakPre [&]  [\<not>] case11B) [|] (Pre [&] case1B [&] case11B)" and hx = " Vinv" and  hy = " Vinv" in SequentialRule, auto)
apply (rule uvwvwafact)
apply (rule uanonfact)
apply (simp add:fOr_def fImp_def)
done

lemma Break1 : "{afterb1 [&] case1B [&] t2 [=] Real 0} move2 {mid2; Vinv}"
apply (simp add:move2_def)
apply (cut_tac qx = "Pre [&] case1B" and hx = "Vinv" in InterruptRule, auto)
apply (cut_tac Break1body) apply (simp add:Quvwv_def)
apply (simp add:BreakPre_def)
apply (subgoal_tac "([\<not>]RVar ''t2''[<]Real T2) = RVar ''t2''[\<ge>]Real T2", auto)
prefer 2
apply (simp add:fNot_def fGreaterEqual_def fLess_def)
apply (metis not_le)
apply (cut_tac  mid2fact  mid212fact3)
apply (simp add:mid211_def mid212_def fAnd_def fImp_def b2_def xa_def ua_def ya_def wa_def exist_def fEx_def)
apply (simp add: fOr_def fEqual_def fGreaterEqual_def fLess_def fGreater_def, auto)
apply blast+
done

lemma Assignfact12 : "{mid2} a := (Real - cmax){Vinv [&] case1B;  Vinv}"
apply (simp add:a_def)
apply (rule AssignRuleR)
apply (simp add:mid2_def Vinv_def case1B_def)
apply (simp add:fImp_def fAnd_def fOr_def fLess_def fGreaterEqual_def fLessEqual_def fEqual_def uv_def wv_def)
done
 
lemma Breakfact12 : " {Vinv [&]case1B}<[(''s''), (''v'')]:[v, a]&&Inv3&v[>]Real 0 > {v [=] Real 0 [&] case1B; Vinv}"
apply (rule ContinuousRule, auto)
apply (simp add:Inv3_def)
apply (subgoal_tac "[\<not>]RVar ''v''[>]Real 0 = RVar ''v''[\<le>]Real 0", auto)
apply (simp add:case1B_def case11B_def fAnd_def fEx_def fImp_def fLessEqual_def fGreaterEqual_def fEqual_def
uv_def wv_def ua_def wa_def)
apply (simp add:fNot_def fLessEqual_def fGreater_def)
apply (metis not_less)
apply (simp add:Inv3_def Vinv_def fImp_def fAnd_def)
done    

lemma SelfCfact1 : "{mid2}SelfC{Pre [&] case1B;  Vinv}"
apply (simp add:SelfC_def)
apply (cut_tac qx = "Vinv [&] case1B " and hx = "Vinv" and hy = "Vinv" in SequentialRule, auto)
apply (cut_tac Assignfact12, auto)
apply (cut_tac qx = "v [=] Real 0 [&] case1B  " and hx = "Vinv" and hy = "Vinv" in SequentialRule, auto)
apply (cut_tac Breakfact12, auto)
apply (rule AssignRuleR)
apply (simp add:fImp_def Pre_def VA_def Vinv_def Ainv_def case11B_def case1B_def)
apply (simp add:fAnd_def fEqual_def fLess_def fGreater_def fLessEqual_def fGreaterEqual_def wa_def uv_def wv_def)
using cmaxdef vmaxdef apply linarith
apply (simp add:fImp_def fOr_def)+
done
 
lemma Fail1 : "{mid2} P2 {Pre [&] case1B;  Vinv}"
apply (simp add:P2_def)
apply (cut_tac qx = "Pre [&] case1B" in IFRule, auto)
apply (cut_tac ax = "mid2" and qx ="Pre [&] case1B" and Hx = "  Vinv" in ConsequenceRule, auto)
apply (rule SelfCfact1)
apply (simp add:fAnd_def fImp_def)
apply (simp add:mid2_def Pre_def case1B_def)
apply (simp add:fImp_def fAnd_def fNot_def fGreaterEqual_def fOr_def fLess_def)
done

lemma Control1 : "{afterb1 [&]case1B [&] t2 [=] Real 0}move2; P2{Pre [&]case1B; Vinv}"
apply (cut_tac qx = "mid2" and hx = " (Vinv)" and hy = "(Vinv)" in SequentialRule, auto)
apply (cut_tac Break1,simp) 
apply (rule Fail1)
apply (simp add:fImp_def fOr_def)
done 

lemma Case1fact : "{afterb1}case1{(Pre [&] case1B) [|] (afterb1 [&] ( [\<not>] case1B));  Vinv}"
apply (simp add:case1_def)
apply (cut_tac qx = "Pre [&] case1B" in IFRule, auto)
defer
apply (simp add:fImp_def fAnd_def fNot_def fOr_def case1B_def)
apply (cut_tac qx = "afterb1 [&] case1B [&] t2 [=] (Real 0)" and hx = "(Vinv)" 
            and hy = "(Vinv)" in SequentialRule, auto)
defer apply (cut_tac Control1, simp)
apply (simp add:fImp_def fOr_def)
apply (rule AssignRuleR)
apply (simp add:afterb1_def Inv1_def Acc1_def Acc2_def)
apply (simp add: Pre_def VA_def Vinv_def Ainv_def fAnd_def case1B_def uv_def wv_def fEqual_def fImp_def afterb1_def b1_def exist_def fOr_def fEx_def fGreater_def fLess_def fGreaterEqual_def fLessEqual_def)
done 

definition case2B:: "fform" where
"case2B == (RVar uv [=] Real 1) [&] (RVar wv [=] Real 0)"
definition case3B :: "fform" where
"case3B == ((RVar uv [=] Real 0) [&] (RVar wv [=] Real 1))"
definition case4B :: "fform" where
"case4B == (([\<not>]case1B) [&] ([\<not>]case2B) [&] ([\<not>]case3B))"

(*Notice that we present the facts for case2, case3, and case4 as axioms rather than proving them
as what we do to case1 above. The reason is that they have very similar structure, 
and the proofs of them are almost the same as case1.*)
axiomatization where
Case2fact : "{(Pre [&] case1B) [|] (afterb1 [&] ( [\<not>] case1B))}case2
{(Pre [&] (case2B [|] case1B)) [|] (afterb1 [&] ( [\<not>] case2B) [&] ( [\<not>] case1B));  Vinv}"
and
Case3fact : "{(Pre [&] (case2B [|] case1B)) [|] (afterb1 [&] ( [\<not>] case2B) [&] ( [\<not>] case1B))}case3
             {(Pre [&] (case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ( [\<not>] case3B)[&] ( [\<not>] case2B) [&] ( [\<not>] case1B));  Vinv}"
and
(*The following fact implies that location 1 is not reachable: the precondition of "Case4fact" in conjunction with the condition of "case4" are not satisfiable. *)
Case4fact : "{(Pre [&] (case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ( [\<not>] case3B)[&] ( [\<not>] case2B) [&] ( [\<not>] case1B))}case4
                   {(Pre [&] (case4B [|] case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ( [\<not>]case4B) [&] ( [\<not>] case3B)[&] ( [\<not>] case2B) [&] ( [\<not>] case1B));   Vinv}"

lemma AllCases : "{afterb1}case1; case2; case3; case4{Pre; Vinv}"
apply (cut_tac qx = "(Pre [&] case1B) [|] (afterb1 [&] ( [\<not>] case1B))" and hx = "(Vinv)" and  hy = "(Vinv)" in SequentialRule, auto)
apply (rule Case1fact)
apply (cut_tac qx = "(Pre [&] (case2B [|] case1B)) [|] (afterb1 [&] ( [\<not>] case2B) [&] ( [\<not>] case1B))" and hx = " (Vinv)" and  hy = "(Vinv)" in SequentialRule, auto)
apply (rule Case2fact)
apply (cut_tac qx = "(Pre [&] (case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ( [\<not>] case3B)[&] ( [\<not>] case2B) [&] ( [\<not>] case1B))" and hx = "(Vinv)" and  hy = "(Vinv)" in SequentialRule, auto)
apply (rule Case3fact)
apply (cut_tac ax = "(Pre [&] (case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ( [\<not>] case3B)[&] ( [\<not>] case2B) [&] ( [\<not>] case1B))" and qx ="(Pre [&] (case4B [|] case3B [|] case2B [|] case1B)) [|] (afterb1 [&] ( [\<not>]case4B) [&] ( [\<not>] case3B)[&] ( [\<not>] case2B) [&] ( [\<not>] case1B))" and Hx = " Vinv" in ConsequenceRule, auto)
apply (rule Case4fact)
apply (simp add:fAnd_def fImp_def fNot_def fOr_def case4B_def, auto)
apply (simp add:fImp_def fOr_def)+
done 

lemma Bodyfact : "{Pre [&] t1 [=] Real 0} body {mid1;  Vinv}"
apply (simp add:body_def)
apply (cut_tac qx = Pre and hx = Vinv in InterruptRule, auto)
apply (cut_tac AllCases) apply (simp add:afterb1_def)
apply (cut_tac mid1fact  mid22fact3)
apply (simp add:mid11_def mid22_def)
apply (subgoal_tac "[\<not>]RVar ''t1''[<]Real T1 = RVar ''t1''[\<ge>]Real T1", auto)
apply (simp add:fImp_def fAnd_def fOr_def)
apply (simp add:b1_def uv_def wv_def fEx_def fAnd_def fImp_def fOr_def, clarsimp)
apply blast
apply (simp add:fGreaterEqual_def fLess_def fNot_def, auto)
done

lemma Assignfact : "{mid1} a := (Real - cmax) {Vinv;   Vinv}"
apply (simp add:a_def mid1_def Vinv_def)
apply (rule AssignRuleR, auto)
apply (simp add:fImp_def fAnd_def fOr_def fLess_def fGreaterEqual_def fLessEqual_def fEqual_def uv_def wv_def)
apply (simp add:fImp_def)
done

lemma Breakfact : "{Vinv} <[(''s''), (''v'')]:[v, a]&&Inv3&v[>]Real 0 > {v [=] Real 0; Vinv}"
apply (rule ContinuousRule, auto)
apply (subgoal_tac "[\<not>]RVar ''v''[>]Real 0 =  RVar ''v''[\<le>]Real 0", simp)
apply (simp add:Inv3_def)
apply (simp add: fImp_def fAnd_def fLessEqual_def fGreaterEqual_def fEqual_def)
apply (simp add:fLessEqual_def fGreater_def fNot_def, auto)
apply (simp add:Vinv_def Inv3_def fImp_def fAnd_def fLessEqual_def fGreaterEqual_def fEx_def)
done

lemma SelfCfact : "{mid1}SelfC{Pre;Vinv}"
apply (simp add:SelfC_def)
apply (cut_tac qx = "Vinv" and hx = "Vinv" and  hy = "Vinv" in SequentialRule, auto)
apply (rule AssignRuleR, auto)
apply (simp add:mid1_def Vinv_def)
apply (simp add:fAnd_def fOr_def fLessEqual_def fLess_def fGreaterEqual_def)
apply (simp add: fImp_def)
apply (cut_tac qx = "v [=] Real 0" and hx = "Vinv" and hy = "Vinv" in SequentialRule, auto)
defer
apply (rule AssignRuleR, auto)
apply (simp add:Pre_def VA_def Vinv_def Ainv_def)
apply (simp add:fEqual_def fImp_def fAnd_def fLessEqual_def fLess_def fGreaterEqual_def fGreater_def)
apply (cut_tac cmaxdef T1def T2def vmaxdef)
apply (smt mult_strict_right_mono vmaxdef)
apply (simp add:fImp_def fOr_def)+
apply (rule ContinuousRule, auto)
apply (simp add:Inv3_def)
apply (subgoal_tac "[\<not>]RVar ''v''[>]Real 0 = RVar ''v''[\<le>]Real 0", auto)
apply (simp add:fImp_def fAnd_def fLessEqual_def fGreaterEqual_def fEqual_def)
apply (simp add:fGreater_def fLessEqual_def fNot_def, auto)
apply (simp add:Vinv_def Inv3_def fImp_def fAnd_def)
done 

lemma Fail : "{mid1} P1 {Pre;   Vinv}"
apply (simp add:P1_def)
apply (cut_tac qx = "Pre"   in IFRule, auto)
apply (cut_tac ax = "mid1" and qx ="Pre" and Hx = " Vinv" in ConsequenceRule, auto)
apply (cut_tac SelfCfact, auto)
apply (simp add:fAnd_def fImp_def)
apply (simp add:mid1_def fImp_def fOr_def)
apply (simp add:Pre_def fAnd_def fNot_def fLess_def fGreaterEqual_def)
done 

lemma Control : " {Pre [&] t1 [=] Real 0}body; P1{Pre;Vinv} "
apply (cut_tac qx = "mid1" and hx = "Vinv" and hy = "Vinv" in SequentialRule, auto)
apply (cut_tac Bodyfact,simp)
apply (simp add:P1_def)
apply (cut_tac qx = Pre in  IFRule, auto)
apply (cut_tac SelfCfact)
apply (rule ConsequenceRule, auto)
apply (simp add:fAnd_def fImp_def)
apply (simp add:fImp_def fOr_def mid1_def)
apply (simp add:Pre_def fAnd_def fNot_def fLess_def fGreaterEqual_def)
apply (simp add:fImp_def fOr_def mid1_def)
done
 
theorem TrainOneLoop : "{Pre}train {Pre; Vinv}"
apply (simp add:train_def)
apply (cut_tac qx = "Pre[&]t1[=]Real 0" and   hx = fFalse and hy =Vinv in SequentialRule, auto)
apply (rule AssignRuleR,auto)
apply (simp add:Pre_def VA_def Vinv_def Ainv_def v_def a_def fImp_def fAnd_def fLessEqual_def fLess_def fGreaterEqual_def
fGreater_def fEqual_def)
apply (simp add:fImp_def)
apply (cut_tac Control,simp)
apply (simp add:fImp_def fOr_def)
done 

(*This is the main theorem stating the safety of the train.*)
(*It shows that the velocity v is always in the range [0, vmax], which implies property F2, as defined in the paper.*)
theorem TrainSpec : "{Pre} train*&&Pre {Pre;Vinv}"
apply (rule RepetitionRule, auto)
apply (rule TrainOneLoop)
apply (simp add:fImp_def)+
done
end