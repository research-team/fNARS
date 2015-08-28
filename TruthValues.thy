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


subsection {* Truth-value functions *}

subsubsection {* Strong syllogism *}

fun F_ded :: "probability \<Rightarrow> probability \<Rightarrow> probability" where
"F_ded prob1 prob2 = (let f1 = f_freq prob1; c1 = c_conf prob1; f2 = f_freq prob2; c2 = c_conf prob2 in
                      probability.make (and2 f1 f2) (and4 f1 f2 c1 c2))"

end