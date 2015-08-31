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

end

