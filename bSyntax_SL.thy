header {* Abstract syntax for First-Order Logic and bHCSP. *}

theory bSyntax_SL 
  imports  Main Real
begin

 
(*Expressions of HCSP language.*)
datatype exp = Real real ("Real _" 75)
             | RVar string   ("RVar _" 75 )
             | Add exp exp   (infixr "[+]" 70)
             | Sub exp exp   (infixl  "[-]" 70)
             | Mul exp exp   (infixr "[*]" 71)
             | Div exp exp   (infixr "[**]" 71) 


(*States*)
type_synonym state = "string  => real"

(*Evaluation of expressions*)
primrec evalE :: "exp \<Rightarrow> state => real" where
"evalE (Real y) f = y" |
"evalE (RVar (x)) f = f x" |
"evalE (e1 [+] e2) f =  (evalE e1 f +  evalE e2 f)" |
"evalE (e1 [-] e2) f = (evalE e1 f -  evalE e2 f)" |
"evalE (e1 [*] e2) f = (evalE e1 f *  evalE e2 f)"

section{*FOL operators*}
type_synonym fform = "state  \<Rightarrow> bool"
definition fTrue:: "fform" where " fTrue == % s. True"
definition fFalse:: "fform" where "fFalse == % s. False"
definition fEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[=]_" 69) where
"e [=] f == % s. evalE e s = evalE f s"
definition fLess :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[<]_" 69) where
"e [<] f == % s. (evalE e s < evalE f s)" 

definition fAnd :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixl "[&]"  65) where
"P [&] Q == % s. P s \<and> Q s"
definition fOr :: "fform\<Rightarrow> fform \<Rightarrow> fform"  (infixl "[|]" 65) where
"P [|] Q == % s. P s \<or> Q s"
definition fNot :: "fform \<Rightarrow> fform"  ("[\<not>]_" 67) where
"[\<not>]P == % s. \<not> P s"
definition fImp :: "fform \<Rightarrow> fform \<Rightarrow> fform"  (infixl "[\<longrightarrow>]" 63) where
"P [\<longrightarrow>] Q == % s. P s \<longrightarrow> Q s"
definition fEx :: "string \<Rightarrow> fform \<Rightarrow> fform" ("[\<exists>]__" 62) where
"[\<exists>]v P == % s. (\<exists> u. (P (%y. if (y=v) then u else s y)))"

definition fLessEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[\<le>]_" 69) where
"e [\<le>] f ==% s. (evalE e s \<le> evalE f s)"
definition fGreaterEqual :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[\<ge>]_" 69) where
"e [\<ge>] f == % s. (evalE e s \<ge> evalE f s)"
definition fGreater :: "exp \<Rightarrow> exp \<Rightarrow> fform"  ("_[>]_" 69) where
"e [>] f == % s. (evalE e s > evalE f s)"

(*close() extends the formula with the boundary, used for continuous evolution.*)
consts close :: "fform \<Rightarrow> fform"

axiomatization where
Lessc[simp]: "close (e [<] f) = e [\<le>] f" and
Greatc[simp]: "close (e [>] f) = e [\<ge>] f" and
Equalc[simp]: "close (e [=] f) = e [=] f" and
GreatEqual[simp] : "close ( e [\<ge>] f) =  e [\<ge>] f" and
LessEqual[simp] : "close ( e [\<le>] f) =  e [\<le>] f" and
Andc[simp]: "close (P [&] Q) = close (P) [&] close (Q)" and
Orc[simp]: "close (P [|] Q) = close (P) [|] close (Q)"


declare fTrue_def [simp]
declare fFalse_def [simp]
     
(*Types for defining bHCSP*)
type_synonym cname = string
type_synonym time = real
type_synonym qname = string
type_synonym qualityp = "fform \<Rightarrow> fform \<Rightarrow> fform"

(*Communication processes of bHCSP*)

datatype bindp
= Send "cname" "exp" "qname"        ("_!!_{_}" [110,108,108] 100)      
| Receive "cname" "exp" "qname"   ("_??_{_}" [110,108, 108] 100) 
 | Binder "qualityp" "bindp" "bindp" ("& _ [_, _]" [110,108,108] 100)

(*bHCSP processes*)
datatype bproc
= Qb "bindp"   ("Qb _" 94)
| "Skip"
| Ass "exp" "exp"          ("_ := _" [99, 95] 94)   
| Seq "bproc" "bproc"                   ("_; _"  [91,90] 90)
| Cond "fform" "bproc"                 ("IF _ _"   [95,94]93)
| CondG "fform" "bproc" "bproc"                 ("IFELSE _ _ _"   [95,94,94]93)
| Par  "bproc" "bproc"                  ("_||_" [90,90]89)
(*Repetition is annotated with invariant*)
| Rep "bproc" "fform"                              ("_*&&_"[91] 90)
(*Continuous evolution is annotated with invariant.*)
| Cont  "(string) list" "exp list" "fform" "fform"               ("<_:_&&_&_>" [95,95,96]94)
| Interp "(string) list" "exp list" "fform" "fform" "bindp"  "bproc" ("<_:_&&_&_>[[__" [95,95,96,95,94]94)
| Nondeter "string" "fform" "bproc"                 ("NON _ : _ _" [95,94,94]93)

(*May-modified variables*)
 

primrec mvarE :: "exp \<Rightarrow> (string ) list " where
"mvarE (Real y)  =[]" |
"mvarE (RVar (x))  =   [x]" |
"mvarE (e1 [+] e2)  = []" |
"mvarE (e1 [-] e2)  = []" |
"mvarE (e1 [*] e2)  = []"  |
"mvarE (e1 [**] e2)  = []"


primrec mvarB :: "bindp \<Rightarrow> (string) list" ("mvarB _")
where 
"mvarB ((ch??x{u})) = mvarE (x) @ [(u)]" |
"mvarB ( (ch!!e{u})) = [(u)]" |
"mvarB ( (&q [a, b])) = mvarB ( a) @ mvarB ( b)"

primrec mvarP :: "bproc \<Rightarrow> (string) list" ("mvarP _")
where 
"mvarP (Qb c)  = mvarB c" |
"mvarP (Skip) = []"|
"mvarP (x:=e) =  mvarE (x)" |
"mvarP (P; Q) = mvarP(P) @ mvarP(Q)" |
"mvarP (IF b P) = mvarP(P)" |
"mvarP (IFELSE b P Q) = mvarP (P) @ mvarP(Q)" |
"mvarP (P || Q) = mvarP (P) @ mvarP (Q)" |
"mvarP (P*&&Inv) = mvarP (P)" |
"mvarP (<v:E &&Inv&D>) = v" |
"mvarP (<v:E &&Inv&D>[[b P) = v @ mvarB (b) @ mvarP (P)" |
"mvarP (NON s : b P) = mvarP (P)"
 

(*Existential quantifiers extension to a list of variables*)
primrec Lex :: "fform => (string) list => fform"  ("Lex _ _")
where
"Lex p [] = p" |
"Lex p (x # xs) = ([\<exists>] x (Lex p xs))"
end

