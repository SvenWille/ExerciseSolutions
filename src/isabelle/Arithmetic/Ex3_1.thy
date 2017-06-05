theory Ex3_1
imports Main 
begin 


primrec pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"pow _ 0 = 1"|
"pow val (Suc n)  = val * pow val n"


theorem pow_mult : "pow x (m * n) = pow (pow x m) n"
proof (induct n)
  case 0
  show ?case by simp
 next 
  fix n
  case (Suc n)
  assume "pow x (m * n) = pow (pow x m) n"
  show "pow x (m * Suc n) = pow (pow x m) (Suc n)"