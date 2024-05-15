
(* Require systme to load defined objects in Nat, Bool and List*)
Require Import Nat Bool List.

Section ind1.

(** 1. Types *)
(* Use "Check" command to learn the type of objects *)
(* Type of natural numbers*)
(* Check the type of 1*)
Check 1.
(* Check the type of 1+2*)
Check 1+2.

(* Syntactic sugar *)
(* "+" is a symbol for add. Can I check the type of it? *)
(* Check +. *)
(* Illegal expression to Check + *)
(* By using "Locate" to search, we can find how "+" is defined. *)
Locate "_ + _ ". 
(* Then system will answer : Notation "n + m" := (add n m) : nat_scope *)
(* It means "+" is the notation for add function in nat_scope, and is an infix operator *)
Check _ + _. 
Check add.

(* to see which notations have been defined in the nat_scope *)
Print Scope nat_scope.

(* If you don't want to use "+" for add anymore *)
Close Scope nat_scope.
(*Check 1+2.*)
(*Type check will fail because this expression can't be recognize anymore*)
(* To open the scope again*)
Open Scope nat_scope.

(* Same for the notations in other scopes*)
Locate "&&".
Check _ && _.
Check andb.

(*    "1" has type "nat".  *)
(*    "nat" has type "Set".  *)
(*    "Set" has type "Type".  *)
(*    "Type" has type "Type". *)
Check nat.
Check Set.
Check Type.

(* Type of boolean *)
Check true. 

(* Type of list*)
(* List of nat *)
Check 3::2::1::0::nil.
(* List of boolean *)
Check (true::nil)::(true::false::nil)::nil.
(* List contains only one type of elements. Otherwise type-checking fails *)
Fail Check (2::true::nil).
(* Directly "Check" the empty list "nil", the system answers "nil : list A where A : Type". It mean nil has the type list for type A, where A can be any defined type *)

Check nil.

(* Type of pair *)
(* a pair of elements of the same type *)
Check (1, 2).
(* Pair of different typed elements *)
Check (true , (1::22::nil)).
(* Pair can be also used to make a pair *)
Check (true , (true, 3)).

(* Type of option *)
(* Option with nat *)
Check Some 2.
Check Some (1, Some true).
(* Same as list, directly check None, the system answer it has option type withany defined type A *)
Check None.

(* Define your own type *)
(* Simple enumerate type*)

(* type color*)
Inductive color : Set :=
| Red
| Orange
| Yellow
| Green
| Blue
| Indigo
| Violet.

Check color. 

Check Red.

(*Type*)

(* Define a recursive type, such as mynat *)

Inductive mynat : Set :=
| myO
| myS (n: mynat).

(* The Type has no inhabitant ?*)
Inductive empty :=. 

(** 2. Functions *)

(* Use wild card _ in definitions*)
Definition is_warm (n: color) : bool :=
  match n with
  | Red | Orange | Yellow => true
  | _ => false
  end.

(* Check the type of function is_warm *)
Check is_warm.
(* The is_warm has type nat->nat, means it is a function that takes a nat and returns a nat*)
(* Check the expression of applying is_warm to value Blue*)
Check is_warm Blue.
(*  By application, the "is_warm Blue" has type nat *)
(*  Check the type of applying function is_warm to any color*)
Check is_warm _.


(* Command "Print" is to print the body of a definition *)
(* Printing the definition of type mynat*)
Print mynat.
(* Printing the definition where construction Red is defined *)
Print Red.
(* Printing the definition of type color*)
Print color.
(* Printing the definition of function is_warm*)
Print is_warm.

(* To define a simple function without giving explicit type of the input and the output *)
(* Coq is able to guess the types are nat by the type of "+"*)
Definition double x := x + x.
Check double. Check add.
Print double.

(* Check the type by giving the wrong type, to see why Coq sais no *)
Fail Check double _ _.
Fail Check double true.

(* Coq type checking env is not build for computation*)
Compute double 5.
(* This is not the real computation, it is performes reduce to the normal form*)

(* To define functions using the pattern mathing *)
(* match ... with ... end. *)
(* Converting bool to 0/1 *)
Definition to_bit b :=
  match b with true => 1 | false => 0 end.

(* wild card is useful in pattern matching*)
(* Defining a new type pairs nat and bool *)
Inductive prod_nat_bool : Type := | mypair (a : nat) (b : bool).

(* To take the first element of a pair of nat and bool *)
Definition fst (p : prod_nat_bool) : nat :=
  match p with
  | mypair n _ => n
  end.

Check fst.

(* Replacing all the other natural numbers with _ *)
Definition is_4 n :=
  match n with
  | 4 => true
  | _ => false
  end.

(* Wrong way to define*)
(* Definition self x := x.*)
(* Correct way to do is ?*)


(* 3. Recursive definition *)

(* To define a list of nat *)
Inductive list_nat : Set :=
| nil0
| cons0 (hd : nat) (tl : list_nat).

(* To add up all the nat in a list of nat *)
Fixpoint sum_all_nat (l : list_nat) : nat :=
  match l with
  | nil0 => O
  | cons0 hd tl => hd + sum_all_nat tl
  end.

(* Wrong way to do recursive calls  *)
(*Fixpoint wrong (l : list_nat) :=
    match l with
    | nil=>0
    | cons x xs=> x + wrong (cons 17 nil)
    end.*)

(* Recursive function that takes two arguments *)
(* n <= m*)
Fixpoint leb (n m : nat) {struct m}: bool :=
  match n, m with
  | O, _ => true
  | S _, O => false
  | S n', S m' => leb n' m'
  end.


(* To choose the principal argument by {struct ...} *)
(* n > m *)
Fixpoint gtb (n m : nat) {struct m}: bool :=
  match m, n with
  | O, _ => true
  | S _, O => false
  | S m', S n' => gtb n' m'
  end.

(* To see pattern matching 2 arguments is actually a syntatic suger *)
(* It pattern matching the first then the second *)
Print gtb.


(* Coq only accepts recursive calls on decreasing argument according to smaller structure *)
(* This is a definition Coq can't see decreasing argument *)
(* Fixpoint foo (x : nat) : nat := *)
(*   match x with *)
(*     | 0 => 0 *)
(*     | S x' => foo ((x' * 2) - (x' * 3)) *)
(* end. *)

(* But we can give proofs to Coq to convince it *)
Require Import Lia ZArith.
Require Import Program.

Program Fixpoint foo (x : nat) {measure x}: nat :=
  match x with
    | 0 => 0
    | S x' => foo ((x' * 2) - (x' * 3))
  end. 
Next Obligation.
  induction x'; lia.
Defined.
Print foo_obligation_2.
Compute foo 9.

Lemma plus_comm : forall (n m : nat), n + m = m + n.
Proof.
refine (PeanoNat.Nat.add_comm).
Qed.

Fail Fixpoint list_min (l : list nat) : option nat :=
  match l with
  | nil => None
  | cons h nil => Some h
  | cons h (cons h' t') => list_min (cons (min h h') t')
  end.
Obligation Tactic := idtac.
Program Fixpoint list_min (l : list nat) {measure (length l)}: option nat :=
  match l with
  | nil => None
  | cons h nil => Some h
  | cons h (cons h' t') => list_min (cons (min h h') t')
  end.
Next Obligation.
  intros. rewrite <- Heq_l. simpl.
  apply PeanoNat.Nat.lt_succ_diag_r.
Defined.
Next Obligation.
  simpl. apply measure_wf. refine Wf_nat.lt_wf.
Defined.


(* Sigma type*)
(* rgb value 0~255 is a subset of type nat, which satisfies the predicate x < 256 *)
(* Definition rgb := {x : nat| x <256}. *)

(* Inductive rgb_color :=
| RGB (r g b:rgb). *)

(* Scheme eq_rect_max := Induction for eq Sort Set.
Print eq_rect_max. Print eq_rect.
Scheme my_nat_ind := Minimality for nat Sort Prop.
Print my_nat_ind.
Definition strange :Type@{Set+1} := forall P:Prop , {P} + {~ P}.
Set Printing Universes.
Check strange. Check sig.
Check Set. Check Prop.  *)

(* Universe X Y Z.
Definition x := Type@{X}.
Definition y := Type@{Y}.
Definition z := Type@{Z}.
Definition dummy:x:y := unit.
Check dummy.
Fail Check y:x. *)