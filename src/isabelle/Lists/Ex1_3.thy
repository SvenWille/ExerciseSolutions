theory Ex1_3 
imports Main
begin 


fun alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where   
"alls _ [] = True"|
"alls cond (x#xs) =  (cond x \<and> alls cond xs)"


fun exs :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where 
"exs cond [] = False"|
"exs cond (x#xs) = (if cond x then True else exs cond xs)"



lemma "alls (\<lambda>x . P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)" 
proof (induct xs)
  show "alls (\<lambda>x. P x \<and> Q x) [] = (alls P [] \<and> alls Q [])" by simp
 next 
  fix a xs 
  assume "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)"
  thus "alls (\<lambda>x. P x \<and> Q x) (a # xs) = (alls P (a # xs) \<and> alls Q (a # xs))" by auto
qed

lemma tmp [simp] : "alls P (xs @ [x]) = (alls P xs \<and> P x)" 
proof (induct xs)
  case Nil 
  show ?case by simp
 next 
  fix a xs 
  case (Cons a xs)
  assume " alls P (xs @ [x]) = (alls P xs \<and> P x)"
  thus ?case by simp
qed

lemma "alls P (rev xs) = alls P xs "
proof (induct xs) 
  case Nil 
  show ?case by simp
 next 
  fix a xs
  case (Cons a xs)

  assume " alls P (rev xs) = alls P xs"
  thus ?case by auto
qed

(*
lemma "exs (\<lambda>x . P x \<and> Q x) xs = (exs P xs \<and> exs Q xs)"
quickcheck
*)

lemma "exs P (map f xs) = exs (P \<circ> f) xs"
proof (induct xs)
  case Nil 
  show ?case by simp
 next 
  fix a xs 
  case (Cons a xs)
  assume a:"exs P (map f xs) = exs (P \<circ> f) xs"

  show "exs P (map f (a # xs)) = exs (P \<circ> f) (a # xs)" 
  proof (cases "P (f a)")
    assume "P (f a)"
    thus " exs P (map f (a # xs)) = exs (P \<circ> f) (a # xs)" by simp
   next 
    assume "\<not> P (f a)"
    with a show  "exs P (map f (a # xs)) = exs (P \<circ> f) (a # xs) "  by simp 
  qed
qed


lemma exs_cons_append [simp] :  "exs P (a#xs) = exs P (xs @ [a])" 
proof (induct xs) 
  case Nil 
  show ?case by simp
 next 
  fix aa xs 
  case (Cons aa xs)
  assume a:"exs P (a # xs) = exs P (xs @ [a])"
  show "exs P (a # aa # xs) = exs P ((aa # xs) @ [a])" 
  proof (cases "P aa")
  assume "P aa"
  thus " exs P (a # aa # xs) = exs P ((aa # xs) @ [a])" by simp
 next 
  assume "\<not>P aa"
  from a show  " exs P (a # aa # xs) = exs P ((aa # xs) @ [a])" by auto
 qed
qed
  

lemma "exs P (rev xs) = exs P xs"
proof (induct xs)
  case Nil 
  show ?case by simp
 next 
  fix a xs 
  case (Cons a xs)
  assume a:"exs P (rev xs) = exs P xs"
  show ?case 
  proof (cases "P a")
    assume "P a"
    with exs_cons_append show  "exs P (rev (a # xs)) = exs P (a # xs)" by fastforce
   next 
    assume "\<not>P a"
    with exs_cons_append and a show "exs P (rev (a # xs)) = exs P (a # xs)" by force
  qed
qed
  

lemma "exs (\<lambda> x . P x \<or> Q x) xs = exs P xs \<or> exs Q xs"
proof (induction xs)
  case Nil
  show ?case by simp
 next 
  fix a xs 
  case (Cons a xs)
  assume hyp:"exs (\<lambda>x. P x \<or> Q x) xs = exs P xs \<or> exs Q xs" 
  show ?case 
  proof (cases "P a")
    assume a:"P a"
    show "exs (\<lambda>x. P x \<or> Q x) (a # xs) = exs P (a # xs) \<or> exs Q (a # xs)" 
    proof (cases "Q a")
      assume "Q a" 
      with a show "exs (\<lambda>x. P x \<or> Q x) (a # xs) = exs P (a # xs) \<or> exs Q (a # xs)" by simp
     next 
      assume "\<not>(Q a)"
      with a and hyp show " exs (\<lambda>x. P x \<or> Q x) (a # xs) = exs P (a # xs) \<or> exs Q (a # xs)" by simp
     qed
    next
     assume "\<not>P a"
     with hyp show " exs (\<lambda>x. P x \<or> Q x) (a # xs) = exs P (a # xs) \<or> exs Q (a # xs)" by force
   qed
qed


lemma "exs P xs = (\<not>(alls (\<lambda> x .\<not> P x) xs))" 
proof (induct xs)
  case Nil 
  show ?case by simp
 next 
  fix a xs 
  case (Cons a xs)
  assume a:"exs P xs = (\<not> alls (\<lambda>x. \<not> P x) xs)" 
  show ?case 
  proof (cases "P a")
    assume "P a"
    thus  "exs P (a # xs) = (\<not> alls (\<lambda>x. \<not> P x) (a # xs))" by simp
   next 
    assume "\<not>P a" 
    with a show "exs P (a # xs) = (\<not> alls (\<lambda>x. \<not> P x) (a # xs))" by simp
  qed
qed

primrec is_in :: "'a list \<Rightarrow> 'a \<Rightarrow> bool" where
"is_in [] _  = False "|
"is_in (x#xs) val = (if  x = val then True else is_in xs val)"

lemma "is_in ls a = exs (\<lambda>x . x = a) ls"
apply (induction ls)
apply simp_all
done

primrec nodups :: "'a list \<Rightarrow> bool" where 
"nodups [] = True"|
"nodups (x#xs)   = (if x \<in> set xs then False else nodups xs)"


primrec deldups :: "'a list \<Rightarrow> 'a list" where 
"deldups [] =  []"|
"deldups (x#xs) = (let tmp =  deldups xs in (if  x \<in> set tmp then tmp else x#tmp) )"


fun deldups2 :: "'a list \<Rightarrow> 'a list" where 
"deldups2 [] =  []"|
"deldups2 (x#xs) =  x # deldups2 (filter (\<lambda>y . y \<noteq> x) xs)"
    
lemma "length (deldups xs ) \<le> length xs"
proof (induct xs)
  case Nil 
  show ?case by simp
 next 
  fix a xs 
  case (Cons a xs) 
  assume a:"length (deldups xs) \<le> length xs"
  show "length (deldups (a # xs)) \<le> length (a # xs) " 
  proof (cases "a \<in> set (deldups xs)")
    assume "a \<in> set (deldups xs)"
    with a show "length (deldups (a # xs)) \<le> length (a # xs)" by simp
   next 
    assume "a \<notin> set (deldups xs)"
    with a show "length (deldups (a # xs)) \<le> length (a # xs)" by simp
  qed
qed

lemma "length (deldups2 xs ) \<le> length xs" 
proof (induct xs)
  case Nil 
  show ?case by simp 
 next 
  fix a xs 
  case (Cons a xs)
  assume hyp:"length (deldups2 xs) \<le> length xs"
  show "length (deldups2 (a # xs)) \<le> length (a # xs)" 
  proof(cases "a \<in> set xs")
    assume "a \<in> set xs"
    with hyp show  "length (deldups2 (a # xs)) \<le> length (a # xs)" 
    
    