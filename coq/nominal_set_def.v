Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Le.
Require Import PeanoNat.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

(** * Nominal Sets *)
(* TODO: intro *)
(** * Groups *)
(* In this section we define groups and prove very basic lemmas about them.
   These lemmas will later be used to simplify statements about group elements. *)

(* Groups are a type having an identity element, an inverse function and an operation on
   elements. The elements respeect the left and right identity as well as inverse laws. *)
Structure group :=
  {
    group_obj :> Type;
    group_id : group_obj;
    group_inv : group_obj -> group_obj;
    group_op : group_obj -> group_obj -> group_obj;
    group_assoc : forall x y z, group_op (group_op x y) z = group_op x (group_op y z);
    group_left_id : forall x, group_op group_id x = x;
    group_right_id : forall x, group_op x group_id = x;
    group_left_inv : forall x, group_op (group_inv x) x = group_id;
    group_right_inv : forall x, group_op x (group_inv x) = group_id;
  }.

Notation "1" := (group_id _).
Notation "x ^-1" := (group_inv _ x) (at level 30, format "x ^-1").
Notation "x * y" := (group_op _ x y).

(* We show that the right inverse is unique in order to prove the following two well known
   lemmas about inverses. These lemmas can be used to simplify goals. *)
Lemma group_inv_unique (G: group) (g h: G) : g * h = 1 -> g^-1 = h.
Proof.
  intros H. rewrite <- (group_right_id _ (g^-1)). rewrite <- H, <- group_assoc.
  now rewrite group_left_inv, group_left_id.
Qed.

Lemma group_inv_id (G: group) : 1^-1 = (group_id G).
Proof.
  apply group_inv_unique. now apply group_left_id.
Qed.

Lemma group_inv_op (G: group) (g h: G) : (g * h)^-1 = h^-1 * g^-1.
Proof.
  apply group_inv_unique. rewrite group_assoc, <- (group_assoc _ h).
  rewrite group_right_inv, group_left_id. now apply group_right_inv.
Qed.

(* A homomorphism between groups G and H is a function from G to H which respects the
   group laws. *)
Structure homomorphism (G H: group) :=
  {
    hom :> G -> H;
    hom_id: hom 1 = 1;
    hom_op: forall x y, hom (x * y) = (hom x) * (hom y);
    hom_inv: forall x, hom (x^-1) = (hom x)^-1;
  }.


(** * G-sets *)
(* Now we define G-sets and show that these are compositional for product, sum and
   function types. *)

(* A G-set is a type X with a group action on X which respects the group structure of G. *)
Structure G_set (G: group) :=
  {
    G_set_X :> Type;
    action: G -> G_set_X -> G_set_X;
    G_set_id: forall x,  (action 1 x) = x;
    G_set_assoc: forall g h x, (action g (action h x)) = (action (g * h) x);
  }.

Notation "g ** x" := (action _ g x) (at level 45, right associativity).

(* We define the tactic gsimpl to simplify goals by using the group and G-set laws. *)
Ltac gsimpl :=
  repeat progress rewrite ?group_left_id, ?group_right_id, ?group_left_inv, ?group_right_inv,
  ?group_inv_id, ?group_inv_op,
  ?G_set_id, ?G_set_assoc.

(* A group element g acts on a pair (x, y) by acting on x and y simpultaneously. *)
Definition prod_action (G: group) (X Y: G_set G) (g: G) (p: X * Y) : X * Y :=
  match p with
  | (x, y) => (g ** x, g ** y)
  end.

Arguments prod_action {G X Y}.

(* Using above action the product of two G-sets X and Y is again a G-set. *)
Canonical Structure G_set_prod (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X * Y)%type prod_action).
- intros [x y]. cbn. now gsimpl.
- intros g h [x y]. cbn. now gsimpl.
Defined.

(* Similar to the action on pairs, g acts on a sum s by acting on the by s encapsulated value. *)
Definition sum_action (G: group) (X Y: G_set G) (g: G) (s: X + Y) : X + Y :=
  match s with
  | inl x => inl (g ** x)
  | inr y => inr (g ** y)
  end.

Arguments sum_action {G X Y}.

(* Above action yields a G-set on the sum of two G-sets. *)
Canonical Structure G_set_sum (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X + Y) sum_action).
- intros [x|y]; cbn; now gsimpl.
- intros g h [x|y]; cbn; now gsimpl.
Defined.

(* We define the following action on functions from G-set X to G-set Y. *)
Definition func_action (G: group) (X Y: G_set G) (g: G) (F: X -> Y) : X -> Y :=
  fun x => g ** F (g^-1 ** x).

Arguments func_action {G X Y}.

(* By this action we obtain a G-set on functions from G-set X to G-set Y. *)
Canonical Structure func (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X -> Y) func_action).
- intros F. unfold func_action. extensionality x. now gsimpl.
- intros g h F. extensionality x. unfold func_action. now gsimpl.
Defined.

(* A function F is called equivariant if the group action and the application of F commute. *)
Definition equiv_func {G: group} {X Y: G_set G} (F: X -> Y) :=
  forall (x: X) (g: G), F (g ** x) = g ** F x.

(* We call a subset (given as predicate P) of a G-set X equivariant if it is closed under
   group actions. *)
Definition equiv_subset (G: group) (X: G_set G) (P: X -> Prop) :=
  forall g x, P x -> P (g ** x).


(** * Permutations *)
(* In this section we define permutations and show that they form a group called Perm.
   For Perm-sets X (G-sets with Perm as underlying group) we define the notion of support
   and use it to state when a name is unused/fresh for a given element of X. *)

(* We use the natural numbers as atoms, i.e. names. This is convenient since for a finite
   structure we can easily find an unused/fresh name. *)
Definition atom := nat.

(* Permutations are bijective functions over atoms. We model this by requiring the existence
   of an inverse function. *)
Structure perm :=
  {
    perm_f:> atom -> atom;
    perm_g: atom -> atom;
    perm_right_inv: forall a, perm_f (perm_g a) = a;
    perm_left_inv: forall a, perm_g (perm_f a) = a;
  }.

(* Permutations form a group. Thus we define identity and inverse permutations, as well as
   the composition operation on permutations. *)
Definition perm_id : perm.
  apply (@Build_perm (@id atom) (@id atom)); intros a; reflexivity.
Defined.

Definition perm_inv (pi: perm) : perm.
  destruct pi as [f g H1 H2]. apply (Build_perm g f H2 H1).
Defined.

Definition perm_op (pi pi': perm) : perm.
  destruct pi as [f g H1 H2]. destruct pi' as [f' g' H3 H4].
  apply (Build_perm (compose f f') (compose g' g)).
  - intros a. unfold compose. now rewrite H3, H1.
  - intros a. unfold compose. now rewrite H2, H4.
Defined.

(* The following axiom states that permutations are uniquely determined by their behavior
   on atoms. *)
Axiom perm_eq : forall (pi pi': perm), (forall a, pi a = pi' a) -> pi = pi'.

(* Using the above definitions we obtain the symmetric group, i.e. group of permutations.
   We denote this group by Perm. *)
Canonical Structure group_perm : group.
apply (@Build_group _ perm_id perm_inv perm_op).
- intros pi1 pi2 pi3. apply perm_eq. intros a. destruct pi1, pi2, pi3. unfold perm_op.
  cbn. now rewrite compose_assoc.
- intros pi. apply perm_eq. intros a. destruct pi. unfold perm_op. cbn.
  now rewrite compose_id_left.
- intros pi. apply perm_eq. intros a. destruct pi. unfold perm_op. cbn.
  now rewrite compose_id_right.
- intros pi. apply perm_eq. intros a. destruct pi. unfold perm_op. cbn.
  unfold id, compose. auto.
- intros pi. apply perm_eq. intros a. destruct pi. unfold perm_op. cbn.
  unfold id, compose. auto.
Defined.

(* We choose a convenient name for the type of Perm-sets. *)
Definition perm_set := G_set group_perm.

(* A list of atoms A supports an element x of a Perm-set X if each permutation which
   holds all elements of A does not change x aswell. This means all atoms which are
   not in A do not play a role in x in some sense. *)
Definition support {X: perm_set} (A: list atom) (x: X) :=
  forall (pi: perm), (forall a, In a A -> pi a = a) -> pi ** x = x.

(* In the special case of functions on Perm-sets we can characterize support more precisely. *)
Lemma support_func (X Y: perm_set) (A: list atom) (F: X -> Y) :
  support A F <-> forall (pi: perm), (forall a, In a A -> pi a = a) -> forall x, F (pi ** x) = pi ** F x.
Proof.
  split; intros H.
  - intros pi H' x. specialize (H pi H').
    assert (E: F (pi ** x) = (pi ** F) (pi ** x)) by now rewrite H.
    rewrite E. cbn. unfold func_action. now gsimpl.
  - intros pi H'. specialize (H (pi^-1)). extensionality x. cbn. unfold func_action.
    rewrite H; gsimpl; auto. intros a Aa. specialize (H' a Aa). destruct pi as [pi pi' Hpi Hpi'].
    now rewrite <- H' at 1.
Qed.

(* If all elements of a Perm-set X are supported, i.e. there is a list A supports the
   element, then then we call X nominal. *)
Definition nominal (X: perm_set) := forall (x: X), { A : _ & support A x}.

(* The predicate supp is the intersection of all supports of the given element x.
   It characterizes the atoms that are relevant for x in some sense. *)
Definition supp {X: perm_set} (x: X) := fun a => forall A, support A x -> In a A.

(* The predicate supp is true only for elements of every support A. *)
Lemma supp_sub_support (X: perm_set) A (x: X) :
  support A x -> forall a, supp x a -> In a A.
Proof.
  intros S a H. apply H, S.
Qed.

(* We say an atom a is fresh in y if it is not in (supp y). This means is not
   relevant for y. *)
Definition atom_freshness {Y: perm_set} a (y: Y) := ~ supp y a.

Notation "a # y" := (atom_freshness a y) (at level 40).

(* In general, x is fresh for y if the intersection of (supp x) and (supp y) is empty.
   So, there is no atom relevant for both of them. *)
Definition freshness {X Y: perm_set} (x: X) (y: Y) :=
  forall a, ~ (supp x a /\ supp y a).


(** ** Finite Permutations *)
(* In this subsection we consider the special case of finite permutations. Those are
   permutations that change only finitely many atoms. *)

(* Finite permutations change only finitely many atoms. *)
Definition fin_perm (pi: perm) := exists l, forall a, ~ In a l -> pi a = a.

(* Transpositions swap two atoms a and b. *)
Definition transp (a b c: atom) :=
  if (Nat.eq_dec c a) then b else if (Nat.eq_dec c b) then a else c.

(* We define a tactic to simplify transpositions. *)
Ltac transpsimpl :=
  match goal with
  | [ |- context C[transp] ] => unfold transp; transpsimpl
  | [ |- context C[Nat.eq_dec ?a ?a] ] => let H := fresh "H" in destruct (Nat.eq_dec a a) as [_|H];
                                                              [| exfalso; apply H; reflexivity]
  | [ |- context C[Nat.eq_dec ?a ?b] ] => let H := fresh "H" in destruct (Nat.eq_dec a b) as [H|H];
                                                              [rewrite H|]
  | _ => try congruence
  end.

(* Transpositions are involutions, i.e. self-invers. *)
Lemma transp_involution a b c : transp a b (transp a b c) = c.
Proof.
  repeat transpsimpl; congruence.
Qed.

(* Clearly, transpositions are permutations. *)
Canonical Structure transp_perm (a b: atom) : perm :=
  Build_perm (transp a b) (transp a b) (transp_involution a b) (transp_involution a b).

(* Especially, transpositions are finite transpositions. *)
Lemma transp_fin_perm (a b: atom) : fin_perm (transp_perm a b).
Proof.
  exists [a;b]. cbn. intros x H. repeat transpsimpl; exfalso; auto.
Qed.

(* We define a tactic to simplify transpositions seen as permutations. *)
Ltac transptac :=
  match goal with
  | [ |- context C[transp_perm] ] => (progress cbn); transptac
  | _ => repeat transpsimpl
  end.

(** * Fresh Names *)
(* In this section we show how to get a fresh name/atom for a element x given a
   support A for x. One possibility is to compute the maximum of A and taking the
   successor of it. This atom is not contained in A and thus fresh for x. *)

Module fresh_atom.
  (* Compute the maximum of al list A by folding A. *)
  Definition max_list A := fold_left max A 0.

  (* Take the successor of the maximum to obtain a new atom. *)
  Definition new_atom A := S (max_list A).

  (* We prove that (fold_left max A) is monotone and increasing for a list A. *)
  Lemma fold_max_mono A n m : n <= m -> fold_left max A n <= fold_left max A m.
  Proof.
    revert n m. induction A as [|a A IH]; auto with arith.
    intros n m H. cbn. now apply IH, Nat.max_le_compat_r.
  Qed.

  Lemma fold_max_inc A b : b <= fold_left max A b.
  Proof.
    induction A as [|a A IH]; auto.
    cbn. eapply le_trans. now apply IH. apply fold_max_mono, Nat.le_max_l.
  Qed.

  (* We use both above lemmas to show that the maximum of A is larger or equal to
     all elements of A. *)
  Lemma all_le A : forall a, In a A -> a <= max_list A.
  Proof.
    induction A as [| b A IH]; intros a; [intros []|intros [E|H]].
    - rewrite E. cbn. apply fold_max_inc.
    - eapply le_trans. now apply IH. cbn. apply fold_max_mono. auto with arith.
  Qed.

  (* Using above lemma we see that the new atom cannot be contained in A. *)
  Lemma new_atom_fresh A a : new_atom A <= a -> ~ In a A.
  Proof.
    intros H H'. eapply Nat.nle_succ_diag_l.
    eapply Nat.le_trans; [exact H | now apply all_le].
  Qed.

  (* Thus, the new atom is a witness for a fresh one. *)
  Lemma fresh_atom A: {a: atom | ~ In a A}.
  Proof.
    exists (new_atom A). intros H. now eapply new_atom_fresh, H.
  Qed.

End fresh_atom.

(* We can show now that if x has a support than we can compute a fresh atom for x
   using the above construcion . *)
Lemma support_fresh_atom (X: perm_set) A (x: X) : support A x -> {a | a # x}.
Proof.
  intros H. destruct (fresh_atom.fresh_atom A) as [a H'].
  exists a. intros Su. unfold supp in Su. apply H', Su, H.
Qed.
