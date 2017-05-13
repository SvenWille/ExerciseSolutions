theory Ex1_1 
imports Main 
begin 

primrec snoc :: "'a list => 'a => 'a list"where 
"snoc [] val = [val]"|
"snoc (x#xs) val = x # snoc xs val"


thm rev.simps

thm append.simps

theorem helper : "snoc (ls @ xs ) x = ls @  snoc xs x"
proof (induct ls)
  case Nil 
  show ?case by simp
 next 
  fix a ls 
  assume " snoc (ls @ xs) x = ls @ snoc xs x"
  thus  "snoc ((a # ls) @ xs) x = (a # ls) @ snoc xs x"  by simp
qed

  

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
proof (induct xs)
  case Nil 
  show ?case by simp
 next
  fix a xs 
  assume "rev (x # xs) = snoc (rev xs) x"
  from this show "rev (x # a # xs) = snoc (rev (a # xs)) x" by (simp add : helper)
qed
