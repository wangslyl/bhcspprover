(* I borrow the implementation from 
    [Title:      Sequents/LK0.thy
     Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
     Copyright   1993  University of Cambridge]

But make a modification to adapt to our application. 
*)

header {* Classical First-Order Sequent Calculus *}

theory DDLK0
imports DLK0
begin

datatype dexp = l | Dur fform ("Dur _" 80)
                  | DR real   ("DR _" 80)
                  | DAdd dexp dexp (infixl "[[+]]" 65)


(*dc formulas*)
datatype dform = DTrue | DFalse 
               | DEq dexp dexp        (infixl "[[=]]" 50)
               | DLess dexp dexp       (infixl "[[<]]" 50)
               | DGreat dexp dexp      (infixl "[[>]]" 50)
               | DNot dform           ("[[~]] _" [40] 40)
               | DConj dform dform    (infixr "[[&]]" 35)
               | DDisj dform dform    (infixr "[[|]]" 30)
               | DImp dform dform      (infixr "[[-->]]" 30)
               | DIff dform dform      (infixr "[[<->]]" 25)
               | DAll string dform      ("DALL _ _ " 10)
               | DEx  string dform      ("DEX _ _" 10) 
               | chop dform dform     (infixr "[^]" 38)

definition
dequal_less  (infixl "[[<=]]" 50) where
"x [[<=]] y == (x [[<]] y) [[|]] (x [[=]] y)"
definition
dequal_greater  (infixl "[[>=]]" 50) where
"x [[>=]] y == (x [[>]] y) [[|]] (x [[=]] y)"
definition
almost ("almost _" 60) where
"almost p == ((Dur p) [[=]] l [[&]] l [[>]] DR 0) "

definition
almostz ("almostz _" 60) where
"almostz p == almost p [[|]] l [[=]] DR 0"

axiomatization where
 (*Propositional rules*)

   dbasic: "$H, P, $G |- $E, P, $F" and
  dconjR: "[| $H|- $E, P, $F;  $H|- $E, Q, $F |] ==> $H|- $E, P [[&]] Q, $F"  and
  dconjL: "$H, P, Q, $G |- $E ==> $H, P [[&]] Q, $G |- $E" and

  ddisjR: "$H |- $E, P, Q, $F ==> $H |- $E, P [[|]] Q, $F" and
  ddisjL: "[| $H, P, $G |- $E;  $H, Q, $G |- $E |] ==> $H, P [[|]] Q, $G |- $E" and
 
  dimpR:  "$H, P |- $E, Q, $F ==> $H |- $E, P [[-->]] Q, $F" and
  dimpL:  "[| $H,$G |- $E,P;  $H, Q, $G |- $E |] ==> $H, P [[-->]] Q, $G |- $E" and

  dnotR:  "$H, P |- $E, $F ==> $H |- $E, [[~]] P, $F" and
  dnotL:  "$H, $G |- $E, P ==> $H, [[~]] P, $G |- $E" and

  dFalseL: "$H, DFalse, $G |- $E" and

  dTrue_def: "DTrue == DFalse [[-->]] DFalse" and
  diff_def:  "P [[<->]] Q == (P [[-->]] Q) [[&]] (Q [[-->]] P)"  

axiomatization where
  (*Quantifiers*)

  dallR:  "(!!x.$H |- $E, P(x), $F) ==> $H |- $E, DALL x P(x), $F" and
  dallL:  "$H, P(t), $G, DALL x P(x) |- $E ==> $H, DALL x P(x), $G |- $E" and

  dexR:   "$H |- $E, P(t), $F, DEX x P(x) ==> $H |- $E, DEX  x P(x), $F" and
  dexL:   "(!!x.$H, P(x), $G |- $E) ==> $H, DEX x P(x), $G |- $E" 

axiomatization where
 
 (*Equality*)

  drefl:  "$H |- $E, a [[=]] a, $F" and
  dsubst: "\<And>G H E. $H(a), $G(a) |- $E(a) ==> $H(b), a [[=]] b, $G(b) |- $E(b)" and

  (* Reflection *)

  deq_reflection:  "|- x [[=]] y ==> (x==y)" and
  diff_reflection: "|- P [[<->]] Q ==> (P==Q)"


(** Structural Rules on formulas are inherited from DLK0.thy **)


ML {*
(*Cut and thin, replacing the right-side formula*)
fun cutR_tac ctxt s i =
  Rule_Insts.res_inst_tac ctxt [((("P", 0), Position.none), s)] [] @{thm cut} i THEN
  rtac @{thm thinR} i

(*Cut and thin, replacing the left-side formula*)
fun cutL_tac ctxt s i =
  Rule_Insts.res_inst_tac ctxt [((("P", 0), Position.none), s)] [] @{thm cut} i THEN
  rtac @{thm thinL} (i + 1)
*}


(** If-and-only-if rules **)
lemma diffR: 
    "[| $H,P |- $E,Q,$F;  $H,Q |- $E,P,$F |] ==> $H |- $E, P [[<->]] Q, $F"
  apply (unfold diff_def)
  apply (assumption | rule dconjR dimpR)+
  done

lemma diffL: 
    "[| $H,$G |- $E,P,Q;  $H,Q,P,$G |- $E |] ==> $H, P [[<->]] Q, $G |- $E"
  apply (unfold diff_def)
  apply (assumption | rule dconjL dimpL dbasic)+
   done

lemma diff_refl: "$H |- $E, (P [[<->]] P), $F"
  apply (rule diffR dbasic)+
  done

lemma dTrueR: "$H |- $E, DTrue, $F"
  apply (unfold dTrue_def)
  apply (rule dimpR)
  apply (rule dbasic)
  done


(** Weakened quantifier rules.  Incomplete, they let the search terminate.**)

lemma dallL_thin: "$H, P(x), $G |- $E ==> $H, DALL x P(x), $G |- $E"
  apply (rule dallL)
  apply (erule thinL)
  done

lemma dexR_thin: "$H |- $E, P(x), $F ==> $H |- $E, DEX x P(x), $F"
  apply (rule dexR)
  apply (erule thinR)
  done

(*The rules of LK*)

lemmas [safe] =
  diffR diffL
  dnotR dnotL
  dimpR dimpL
  ddisjR ddisjL
  dconjR dconjL
  dFalseL dTrueR
  drefl dbasic
ML {* val dprop_pack = Cla.get_pack @{context} *}

lemmas [safe] = dexL dallR
lemmas [unsafe] = the_equality dexR_thin dallL_thin
ML {* val dLK_pack = Cla.get_pack @{context} *}

ML {*
  val dLK_dup_pack =
    Cla.put_pack dprop_pack @{context}
    |> fold_rev Cla.add_safe @{thms dallR dexL}
    |> fold_rev Cla.add_unsafe @{thms dallL dexR the_equality}
    |> Cla.get_pack;
*}

method_setup dfast_prop =
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.fast_tac (Cla.put_pack dprop_pack ctxt))) *}

method_setup dfast_dup =
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.fast_tac (Cla.put_pack dLK_dup_pack ctxt))) *}

method_setup dbest_dup =
  {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (Cla.best_tac (Cla.put_pack dLK_dup_pack ctxt))) *}

method_setup lem = {*
  Attrib.thm >> (fn th => fn _ =>
    SIMPLE_METHOD' (fn i =>
      rtac (@{thm thinR} RS @{thm cut}) i THEN
      REPEAT (rtac @{thm thinL} i) THEN
      rtac th i))
*}


lemma dmp_R:
  assumes dmajor: "$H |- $E, $F, P [[-->]] Q"
    and dminor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule thinRS [THEN cut], rule dmajor)
  apply step
  apply (rule thinR, rule dminor)
  done

lemma dmp_L:
  assumes dmajor: "$H, $G |- $E, P [[-->]] Q"
    and dminor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule thinL [THEN cut], rule dmajor)
  apply step
  apply (rule thinL, rule dminor)
  done


(** Two rules to generate left- and right- rules from implications **)

lemma dR_of_imp:
  assumes dmajor: "|- P [[-->]] Q"
    and dminor: "$H |- $E, $F, P"
  shows "$H |- $E, Q, $F"
  apply (rule dmp_R)
   apply (rule_tac [2] dminor)
  apply (rule thinRS, rule dmajor [THEN thinLS])
  done

lemma dL_of_imp:
  assumes dmajor: "|- P [[-->]] Q"
    and dminor: "$H, $G, Q |- $E"
  shows "$H, P, $G |- $E"
  apply (rule dmp_L)
   apply (rule_tac [2] dminor)
  apply (rule thinRS, rule dmajor [THEN thinLS])
  done

(*Can be used to create implications in a subgoal*)
lemma dbackwards_impR:
  assumes prem: "$H, $G |- $E, $F, P [[-->]] Q"
  shows "$H, P, $G |- $E, Q, $F"
  apply (rule dmp_L)
   apply (rule_tac [2] dbasic)
  apply (rule thinR, rule prem)
  done

lemma dconjunct1: "|-P [[&]] Q ==> |-P"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma dconjunct2: "|-P [[&]] Q ==> |-Q"
  apply (erule thinR [THEN cut])
  apply fast
  done

lemma dspec: "|- (DALL x P(x)) ==> |- P(x)"
  apply (erule thinR [THEN cut])
  apply fast
  done


(** Equality **)

lemma dsym: "|- a [[=]] b [[-->]] b [[=]] a"
  by (safe add!: dsubst)

lemma dtrans: "|- a [[=]] b [[-->]] b [[=]] c [[-->]] a [[=]] c"
   by (safe add!: dsubst)

(* Symmetry of equality in hypotheses *)
lemmas dsymL =dsym [THEN dL_of_imp]

(* Symmetry of equality in hypotheses *)
lemmas dsymR = dsym [THEN dR_of_imp]

lemma dtransR: "[| $H|- $E, $F, a [[=]] b;  $H|- $E, $F, b [[=]] c |] ==> $H|- $E, a [[=]] c, $F"
  by (rule dtrans [THEN dR_of_imp, THEN dmp_R])

(* Two theorms for rewriting only one instance of a definition:
   the first for definitions of formulae and the second for terms *)

lemma ddef_imp_iff: "(A == B) ==> |- A [[<->]] B"
  apply unfold
  apply (rule diff_refl)
  done

lemma dmeta_eq_to_obj_eq: "(A == B) ==> |- A [[=]] B"
  apply (unfold)
  apply (rule drefl)
  done

(*New added axioms for formulas of DC expressions are not specified here, since the expressions form are limited.*)
(*Arith*)

end
