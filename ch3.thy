theory "ch3"
imports Main
begin
  type_synonym uname = string
  datatype aexp = N int | V uname | Plus aexp aexp

  type_synonym val = int
  type_synonym state = "uname => val"

  fun aval :: "aexp => state => val" where
    "aval (N x) _ = x" |
    "aval (V n) s = s n" |
    "aval (Plus e f) s = aval e s + aval f s"

  fun asimp_const :: "aexp => aexp" where
    "asimp_const (N x) = N x" |
    "asimp_const (V x) = V x" |
    "asimp_const (Plus e f) =
      (case (asimp_const e, asimp_const f) of
        (N ne, N nf) => N (ne + nf) |
        (e, f) => Plus e f)"

  lemma "aval (asimp_const e) s = aval e s"
    apply(induction e)
    apply(auto split: aexp.split)
    done

  fun plus :: "aexp => aexp => aexp" where
    "plus (N n1) (N n2) = N (n1 + n2)" |
    "plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
    "plus a (N i) = (if i = 0 then a else Plus a (N i))" |
    "plus e f = Plus e f"

  lemma aval_plus : "aval (plus e f) s = aval e s + aval f s"
    apply(induction rule: plus.induct)
    apply(auto)
    done

  lemma plus_assoc : "aval (plus (plus e f) g) s = aval (plus e (plus f g)) s"
    apply(auto simp add: aval_plus)
    done

  fun asimp :: "aexp => aexp" where
    "asimp (N n) = N n" |
    "asimp (V v) = V v" |
    "asimp (Plus e f) = plus e f"

  lemma "aval (asimp e) s = aval e s"
    apply(induction e)
    apply(auto simp add: aval_plus)
    done

  fun no_plus_nums :: "aexp => bool" where
    "no_plus_nums (N x) = True" |
    "no_plus_nums (V x) = True" |
    "no_plus_nums (Plus (N n1) (N n2)) = False" |
    "no_plus_nums (Plus e f) = conj (no_plus_nums e) (no_plus_nums f)"

  lemma "no_plus_nums (asimp_const e)"
    apply(induction e)
    apply(auto split: aexp.split)
    done
  
  (* Sum a list of terms *)
  fun sum_terms :: "aexp list => aexp => aexp" where
    "sum_terms [] x = x" |
    "sum_terms (t # ts) x = Plus t (sum_terms ts x)"
  
  lemma "aval (sum_terms xs x) s = sum_list (map (\<lambda> e. aval e s) xs) + aval x s"
    apply(induction xs)
    apply(auto simp add: aval_plus)
    done

  lemma sumterms_app : "aval (sum_terms (x @ y) (N (z1 + z2))) s = aval (sum_terms x (N z1)) s + aval (sum_terms y (N z2)) s"
    apply(induction x)
    apply(auto simp add: aval_plus)
    apply(induction y)
    apply(auto)
    done
  
  (* Split a term into a list of non-constant terms + a total constant *)
  fun split :: "aexp => aexp list*int" where
    "split (N x) = ([], x)" |
    "split (V x) = ([V x], 0)" |
    "split (Plus e f) =
      (case (split e, split f) of
        ((es, en),(fs, fn)) => (es @ fs, en + fn))"

  fun is_var :: "aexp => bool" where
    "is_var (V _) = True" |
    "is_var _ = False"

  fun all_vars :: "aexp list => bool" where
    "all_vars xs = list_all is_var xs"

  lemma split_allvars : "all_vars (fst (split e))"
    apply(induction e)
    apply(auto split: prod.split)
    done

  lemma "aval (sum_terms (fst (split e)) (N (snd (split e)))) s  = aval e s"
    apply(induction e)
    apply(auto split: prod.split simp add: sumterms_app)
    done
  
  fun full_asimp :: "aexp => aexp" where
    "full_asimp exp =
      sum_terms (fst (split exp)) (N (snd (split exp)))"

  lemma "aval (full_asimp x) s = aval x s"
    apply(induction x)
    apply(auto split: prod.split list.split simp add: aval_plus sumterms_app)
    done

  (* So.. full_simp is valid in the sense of preserving value. That's cool, but does it get ALL constants? *)

  fun number_of_consts :: "aexp => nat" where
    "number_of_consts (N i) = 1" |
    "number_of_consts (V _) = 0" |
    "number_of_consts (Plus x y) = number_of_consts x + number_of_consts y"

  lemma var_zero_consts : "is_var a --> number_of_consts a = 0"
    apply(induction a)
    apply(auto)
    done

  lemma all_vars_consts : "all_vars xs ==> number_of_consts (sum_terms xs (N n)) = Suc 0"
    apply(induction xs)
    apply(auto simp add: var_zero_consts)
    done

  lemma split_consts : "number_of_consts (sum_terms (fst (split e)) (N (snd (split e)))) = Suc 0"
    apply(rule all_vars_consts)
    apply(rule split_allvars)
    done

  lemma "number_of_consts (full_asimp e) = 1"
    apply(simp)
    apply(rule split_consts)
    done
end