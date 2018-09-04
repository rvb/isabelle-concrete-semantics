theory "ch2"
  imports Main
begin
fun add2 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add2 0 n = n " |
"add2 (Suc m) n = Suc (add2 m n)"

lemma add2_assoc [simp]: "add2 (add2 x y) z = add2 x (add2 y z)"
  apply(induction x)
  apply(auto)
  done

lemma add2_0rneutral [simp] : "add2 x 0 = x"
  apply(induction x)
  apply(auto)
  done

lemma add2_rightsucc [simp] : "Suc (add2 x y) = add2 x (Suc y)"
  apply(induction x)
  apply(auto)
  done

lemma add2_comm [simp]: "add2 x y = add2 y x"
  apply(induction x)
  apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc m) = Suc (Suc (double m))"

lemma double_correct : "double x = add2 x x"
  apply(induction x)
  apply(auto)
  done

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0" |
"count x (y # xs) = (if x = y then count x xs + 1 else count x xs)"

lemma count_bounded_length : "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

fun snoc :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"snoc x [] = [x]" |
"snoc x (y # xs) = y # snoc x xs"

fun snocrev :: " 'a list \<Rightarrow> 'a list" where
"snocrev [] = []" |
"snocrev (x # xs) = snoc x (snocrev xs)"

lemma snocrev_snoc [simp] : "snocrev (snoc x xs) = x # snocrev xs"
  apply(induction xs)
  apply(auto)
  done

lemma snocrev_self_inverse : "snocrev (snocrev xs) = xs"
  apply(induction xs)
  apply(auto)
  done

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc m) = (Suc m) + sum_upto m"

lemma sum_upto_closed_form : "sum_upto m = m * (m + 1) div 2"
  apply(induction m)
  apply(auto)
  done

datatype 'a tree = Tip | Node "'a tree * 'a * 'a tree"

fun mirror :: "'a tree => 'a tree" where
  "mirror Tip = Tip" |
  "mirror (Node (l, v, r)) = Node (mirror r, v, mirror l)"

fun contents :: "'a tree => 'a list" where
  "contents Tip = []" |
  "contents (Node (l, v, r)) = v # (contents l @ contents r)"

fun sum_tree :: "nat tree => nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node (l, v, r)) = sum_tree l + v + sum_tree r"

lemma sum_tree_contents : "sum_tree x = sum_list (contents x)"
  apply(induction x)
  apply(auto)
  done

datatype 'a tree2 = Tip 'a | Node "'a tree2 * 'a * 'a tree2"

fun mirror2 :: "'a tree2 => 'a tree2" where
  "mirror2 (Tip x) = Tip x" |
  "mirror2 (Node (l,v,r)) = Node (mirror2 r, v, mirror2 l)"

fun preorder :: "'a tree2 => 'a list" where
  "preorder (Tip x) = [x]" |
  "preorder (Node (l,v,r)) = v # (preorder l @ preorder r)" 

fun postorder :: "'a tree2 => 'a list" where
  "postorder (Tip x) = [x]" |
  "postorder (Node (l,v,r)) = snoc v (postorder l @ postorder r)"

(* This one is needed because we're using snoc and so have no
   builtin simplification rules. *)
lemma snoc_rev_simp [simp] : "rev (snoc x xs) = x # rev xs"
  apply(induction xs)
  apply(auto)
  done

lemma "preorder (mirror2 t) = rev (postorder t)"
  apply(induction t)
  apply(auto)
  done

fun intersperse :: "'a => 'a list => 'a list" where
  "intersperse _ [] = []" |
  "intersperse _ [x] = [x]" |
  "intersperse x (y # ys) = y # x # intersperse x ys"

lemma "map f (intersperse x xs) = intersperse (f x) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto)
  done

fun itadd :: "nat => nat => nat" where
  "itadd 0 m = m" |
  "itadd (Suc m) n = itadd m (Suc n)"

(* Obviously, we want to prove this thing correct, so... 
  Proof notes:
  We need to allow n to be arbitrary in the induction hypothesis,
  otherwise the proof doesn't go through in the induction step.
  We delete the add2_comm rule, to stop auto trying to apply it.
  When it does, we end up with the add2 on the rhs in the wrong shape,
  which stops us applying the induction hypothesis and finishing the proof.
*)
lemma "itadd m n = add2 m n"
  apply(induction m arbitrary: n)
  apply(auto simp del: add2_comm)
  done

datatype tree0 = Tip | Node "tree0 * tree0"

fun explode :: "nat => tree0 => tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node (t, t))"

fun nodes :: "tree0 => nat" where
  "nodes Tip = 1" |
  "nodes (Node (l, r)) = nodes l + nodes r + 1"

lemma "nodes (explode n t) = 2^n * (nodes t) + 2^n - 1"
  apply(induction n arbitrary: t)
  apply(auto simp add: algebra_simps)
  done

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp => int => int" where
  "eval Var x = x" |
  "eval (Const y) x = y" |
  "eval (Add y z) x = eval y x + eval z x" |
  "eval (Mult y z) x = eval y x * eval z x"

fun evalp :: "int list => int => int" where
  "evalp [] x = 0" |
  "evalp (c # cs) x = c + x * (evalp cs x)"

fun add_coeffs :: "int list => int list => int list" where
  "add_coeffs [] xs = xs" |
  "add_coeffs xs [] = xs" |
  "add_coeffs (x # xs) (y # ys) = (x + y) # add_coeffs xs ys"

fun mul_coeffs :: "int list => int list => int list" where
  "mul_coeffs [] xs = []" |
  "mul_coeffs (y # ys) xs = add_coeffs (map (\<lambda> z . y * z) xs) (0 # mul_coeffs ys xs)"

fun coeffs :: "exp => int list" where
  "coeffs Var = [0, 1]" |
  "coeffs (Const x) = [x]" |
  "coeffs (Add x y) = add_coeffs (coeffs x) (coeffs y)" |
  "coeffs (Mult x y) = mul_coeffs (coeffs x) (coeffs y)"

(*Note to self: SERIOUSLY use the right induction rules please.*)
lemma evalp_addcoeffs [simp] : "evalp (add_coeffs xs ys) x = evalp xs x + evalp ys x"
  apply(induction rule: add_coeffs.induct)
  apply(auto simp add: algebra_simps)
  done

lemma evalp_scaling [simp] : "evalp (map (( * ) y) xs) x = y * evalp xs x"
  apply(induction xs)
  apply(auto simp add: algebra_simps)
  done

lemma evalp_mulcoeffs [simp] : "evalp (mul_coeffs xs ys) x = evalp xs x * evalp ys x"
  apply(induction rule: mul_coeffs.induct)
  apply(auto simp add: algebra_simps)
  done

lemma "evalp (coeffs e) x = eval e x"
  apply(induction e)
  apply(auto)
  done
end