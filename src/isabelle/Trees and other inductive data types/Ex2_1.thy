theory Ex2_1 
  imports Main 
begin 
  
  
datatype 'a tree = Leaf 'a  | Branch 'a "'a tree"  "'a tree"
  
primrec preOrder :: "'a tree \<Rightarrow> 'a list" where 
  "preOrder (Leaf val) = [val]"|
  "preOrder (Branch val lft rgt) = val #  preOrder lft  @ preOrder rgt"
  
primrec postOrder :: "'a tree \<Rightarrow> 'a list" where 
  "postOrder (Leaf val) = [val]"|
  "postOrder (Branch val lft rgt) = postOrder lft @ postOrder rgt @ [val]"
  
  
primrec inOrder :: "'a tree \<Rightarrow> 'a list" where 
  "inOrder (Leaf val) = [val]"|
  "inOrder (Branch val lft rgt) = inOrder lft @ val # inOrder rgt"
  
primrec mirror :: "'a tree \<Rightarrow> 'a tree" where 
  "mirror (Leaf val) = (Leaf val)"|
  "mirror (Branch val lft rgt) = Branch val (mirror rgt) (mirror lft) "
  
  (*
lemma "inOrder (mirror t) = rev (inOrder t)" 
proof (induct t)
  case (Leaf x)
  then show ?case by simp
next
  case (Branch x1a t1 t2)
  assume "inOrder (mirror t1) = rev (inOrder t1)"
  assume "inOrder (mirror t2) = rev (inOrder t2)"
    
   
qed
  *)
  
primrec root :: "'a tree \<Rightarrow> 'a" where 
  "root (Leaf val) = val"|
  "root (Branch val _ _) = val"
  
primrec leftmost :: "'a tree \<Rightarrow> 'a" where 
  "leftmost (Leaf val) = val"|
  "leftmost (Branch _ lft _) = leftmost lft"
  
primrec rightmost :: "'a tree \<Rightarrow> 'a" where 
  "rightmost (Leaf val) = val"|
  "rightmost (Branch _ _ rgt) = rightmost rgt"  
  