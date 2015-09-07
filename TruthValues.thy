section {* Definitions regarding truth value calculations *}

theory TruthValues
imports Complex_Main
begin

subsection {* Extended Boolean operations *}

definition not :: "real \<Rightarrow> real" where "not x \<equiv> 1.0 - x"

definition and2 :: "real \<Rightarrow> real \<Rightarrow> real"                 where "and2 x y     \<equiv> x * y"
definition and3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"         where "and3 x y z   \<equiv> x * y * z"
definition and4 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where "and4 w x y z \<equiv> w * x * y * z"

definition or2 :: "real \<Rightarrow> real \<Rightarrow> real"                 where "or2 x y     \<equiv> 1.0 - (1.0 - x)*(1.0 - y)"
definition or3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real"         where "or3 x y z   \<equiv> 1.0 - (1.0 - x)*(1.0 - y)*(1.0 - z)"
definition or4 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where "or4 w x y z \<equiv> 1.0 - (1.0 - w)*(1.0 - x)*(1.0 - y)*(1.0 - z)"


subsection {* The k parameter of NAL logic *}

definition k_param :: int where "k_param \<equiv> 2"


subsection {* Truth value representations *}

record evidence =
  w_plus :: int
  w_total :: int

record probability =
  f_freq :: real (* frequency, w+/w *)
  c_conf :: real (* confidence, w/(w+k) *)


subsection {* Conversions between different truth value representations *}

fun ev_to_prob :: "evidence \<Rightarrow> probability" where
"ev_to_prob ev = (let w = w_total ev; f = w_plus ev / w; c = w / (w + k_param) in probability.make f c)"

text {* A shortcut for floor function. *}
definition floor_real :: "real \<Rightarrow> int" where "floor_real \<equiv> Real.floor_ceiling_real_inst.floor_real"

fun prob_to_ev :: "probability \<Rightarrow> evidence" where
"prob_to_ev p = (let f = f_freq p; c = c_conf p; k = real_of_int k_param; wp = k*f*c/(1 - c); w = k*c/(1 - c) in evidence.make (floor_real wp) (floor_real w))"

subsection {* Truth-value functions *}

subsubsection {* Local inference *}

text {* Revision. *}
fun F_rev :: "evidence \<Rightarrow> evidence \<Rightarrow> evidence" where
"F_rev ev1 ev2 = (let w_plus1 = w_plus ev1; w1 = w_total ev1; w_minus1 = w1 - w_plus1;
                      w_plus2 = w_plus ev2; w2 = w_total ev2; w_minus2 = w2 - w_plus2;
                      w_plus  = w_plus1 + w_plus2; w_minus = w_minus1 + w_minus2
                  in evidence.make w_plus (w_plus + w_minus))"


subsubsection {* Immediate inference *}

text {* Negation. *}
fun F_neg :: "probability \<Rightarrow> probability" where
"F_neg prob1 = (let ev1      = prob_to_ev prob1;
                    w_plus1  = w_plus ev1;
                    w1       = w_total ev1;
                    w_minus1 = w1 - w_plus1;
                    w_plus   = w_minus1;
                    ev2      = evidence.make w_plus w1
                in ev_to_prob ev2)"

text {* Conversion. *}
fun F_cnv :: "probability \<Rightarrow> probability" where
"F_cnv prob1 = (let f1 = f_freq prob1; c1 = c_conf prob1;
                    w_plus = floor_real (and2 f1 c1);
                    ev2    = evidence.make w_plus w_plus (* w_minus = 0 *)
                in ev_to_prob ev2)"

text {* Contraposition. *}
fun F_cnt :: "probability \<Rightarrow> probability" where
"F_cnt prob1 = (let f1 = f_freq prob1; c1 = c_conf prob1;
                    w_minus = floor_real (and2 (not f1) c1);
                    ev2     = evidence.make 0 w_minus (* w_plus = 0 *)
                in ev_to_prob ev2)"


subsubsection {* Strong syllogism *}

text {* Deduction. *}
fun F_ded :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_ded prob1 prob2 = (let f1 = f_freq prob1; c1 = c_conf prob1; f2 = f_freq prob2; c2 = c_conf prob2 in
                      probability.make (and2 f1 f2) (and4 f1 f2 c1 c2))"

text {* Analogy. *}
fun F_ana :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_ana prob1 prob2 = (let f1 = f_freq prob1; c1 = c_conf prob1; f2 = f_freq prob2; c2 = c_conf prob2 in
                      probability.make (and2 f1 f2) (and3 f2 c1 c2))"

text {* Resemblance. *}
fun F_res :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_res prob1 prob2 = (let f1 = f_freq prob1; c1 = c_conf prob1; f2 = f_freq prob2; c2 = c_conf prob2 in
                      probability.make (and2 f1 f2) (and3 (or2 f1 f2) c1 c2))"


subsubsection {* Weak syllogism *}

text {* Abduction. *}
fun F_abd :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_abd prob1 prob2 = (let f1 = f_freq prob1;
                          c1 = c_conf prob1;
                          f2 = f_freq prob2;
                          c2 = c_conf prob2;
                          w_plus = floor_real (and4 f1 f2 c1 c2);
                          w = floor_real (and3 f1 c1 c2) in
                      ev_to_prob (evidence.make w_plus w))"

text {* Induction. *}
fun F_ind :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_ind prob1 prob2 = (let f1 = f_freq prob1;
                          c1 = c_conf prob1;
                          f2 = f_freq prob2;
                          c2 = c_conf prob2;
                          w_plus = floor_real (and4 f1 f2 c1 c2);
                          w = floor_real (and3 f2 c1 c2) in
                      ev_to_prob (evidence.make w_plus w))"

text {* Exemplification. *}
fun F_exe :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_exe prob1 prob2 = (let f1 = f_freq prob1;
                          c1 = c_conf prob1;
                          f2 = f_freq prob2;
                          c2 = c_conf prob2;
                          w_plus = floor_real (and4 f1 f2 c1 c2);
                          w = floor_real (and4 f1 f2 c1 c2) in
                      ev_to_prob (evidence.make w_plus w))"

text {* Comparison. *}
fun F_com :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_com prob1 prob2 = (let f1 = f_freq prob1;
                          c1 = c_conf prob1;
                          f2 = f_freq prob2;
                          c2 = c_conf prob2;
                          w_plus = floor_real (and4 f1 f2 c1 c2);
                          w = floor_real (and3 (or2 f1 f2) c1 c2) in
                      ev_to_prob (evidence.make w_plus w))"


subsubsection {* Term composition *}

text {* Intersection. *}
fun F_int :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_int prob1 prob2 = (let f1 = f_freq prob1; c1 = c_conf prob1; f2 = f_freq prob2; c2 = c_conf prob2 in
                      probability.make (and2 f1 f2) (and2 c1 c2))"

text {* Union. *}
fun F_uni :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_uni prob1 prob2 = (let f1 = f_freq prob1; c1 = c_conf prob1; f2 = f_freq prob2; c2 = c_conf prob2 in
                      probability.make (or2 f1 f2) (and2 c1 c2))"

text {* Difference. *}
fun F_dif :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_dif prob1 prob2 = (let f1 = f_freq prob1; c1 = c_conf prob1; f2 = f_freq prob2; c2 = c_conf prob2 in
                      probability.make (and2 f1 (not f2)) (and2 c1 c2))"

end





