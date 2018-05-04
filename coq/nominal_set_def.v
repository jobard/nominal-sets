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

Structure homomorphism (G H: group) :=
  {
    hom :> G -> H;
    hom_id: hom 1 = 1;
    hom_op: forall x y, hom (x * y) = (hom x) * (hom y);
    hom_inv: forall x, hom (x^-1) = (hom x)^-1;
  }.


(** * G-sets *)

(* A G-set is a set X with a group action on X which respects the group structure. *)
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

Definition equiv_func {G: group} {X Y: G_set G} (F: X -> Y) :=
  forall (x: X) (g: G), F (g ** x) = g ** F x.

Definition prod_action (G: group) (X Y: G_set G) (g: G) (p: X * Y) : X * Y :=
  match p with
  | (x, y) => (g ** x, g ** y)
  end.

Arguments prod_action {G X Y}.

Canonical Structure cartesian_prod (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X * Y)%type prod_action).
- intros [x y]. cbn. now gsimpl.
- intros g h [x y]. cbn. now gsimpl.
Defined.

Definition union_action (G: group) (X Y: G_set G) (g: G) (s: X + Y) : X + Y :=
  match s with
  | inl x => inl (g ** x)
  | inr y => inr (g ** y)
  end.

Arguments union_action {G X Y}.

Canonical Structure disjoint_union (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X + Y) union_action).
- intros [x|y]; cbn; now gsimpl.
- intros g h [x|y]; cbn; now gsimpl.
Defined.

Definition func_action (G: group) (X Y: G_set G) (g: G) (F: X -> Y) : X -> Y :=
  fun x => g ** F (g ^-1 ** x).

Arguments func_action {G X Y}.

Canonical Structure func (G: group) (X Y: G_set G) : G_set G.
apply (@Build_G_set G (X -> Y) func_action).
- intros F. unfold func_action. extensionality x. now gsimpl.
- intros g h F. extensionality x. unfold func_action. now gsimpl.
Defined.

Definition equiv_subset (G: group) (X: G_set G) (P: X -> Prop) :=
  forall g x, P x -> P (g ** x).


(** * Permutations *)

(* We use the natural numbers as atoms, i.e. names. This is convenient since for a finite
structure we can easily find an unused name. *)
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

Definition perm_set := G_set group_perm.

(* A predicate on atoms supports an element x of a Perm-set X if the action of every permutation
which is the identity on elements of A does not change x aswell. *)
Definition support {X: perm_set} (A: list atom) (x: X) :=
  forall (pi: perm), (forall a, In a A -> pi a = a) -> pi ** x = x.

(* If all elements of a Perm-set X are fintely supported (there is a finte predicate that
supports the element) then then we call X a nominal set. *)
Definition nominal (X: perm_set) := forall (x: X), { A : _ & support A x}.

(* The predicate supp is the intersection of all predicates that support the given element x. *)
Definition supp {X: perm_set} (x: X) := fun a => forall A, support A x -> In a A.

Lemma supp_sub_support (X: perm_set) A (x: X) :
  support A x -> forall a, supp x a -> In a A.
Proof.
  intros S a H. apply H, S.
Qed.

Definition freshness {X Y: perm_set} (x: X) (y: Y) :=
  forall a, ~ (supp x a /\ supp y a).

Definition atom_freshness {Y: perm_set} a (y: Y) := ~ supp y a.

Notation "a # y" := (atom_freshness a y) (at level 40).

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


(** * Finite Permutations *)

Definition fin_perm (pi: perm) := exists l, forall a, ~ In a l -> pi a = a.

Definition transp (a b c: atom) :=
  if (Nat.eq_dec c a) then b else if (Nat.eq_dec c b) then a else c.

Ltac transpsimpl :=
  match goal with
  | [ |- context C[transp] ] => unfold transp; transpsimpl
  | [ |- context C[Nat.eq_dec ?a ?a] ] => let H := fresh "H" in destruct (Nat.eq_dec a a) as [_|H];
                                                              [| exfalso; apply H; reflexivity]
  | [ |- context C[Nat.eq_dec ?a ?b] ] => let H := fresh "H" in destruct (Nat.eq_dec a b) as [H|H];
                                                              [rewrite H|]
  | _ => try congruence
  end.

Lemma transp_involution a b c : transp a b (transp a b c) = c.
Proof.
  repeat transpsimpl; congruence.
Qed.

Canonical Structure transp_perm (a b: atom) : perm :=
  Build_perm (transp a b) (transp a b) (transp_involution a b) (transp_involution a b).

Lemma transp_fin_perm (a b: atom) : fin_perm (transp_perm a b).
Proof.
  exists [a;b]. cbn. intros x H. repeat transpsimpl; exfalso; auto.
Qed.

Ltac transptac :=
  match goal with
  | [ |- context C[transp_perm] ] => (progress cbn); transptac
  | _ => (* try apply f_equal; *) repeat transpsimpl
  end.


Module fresh_atom.
  Definition max_list l := fold_left max l 0.
  Definition new_atom l := S (max_list l).

  Lemma fold_max_mono l n m : n <= m -> fold_left max l n <= fold_left max l m.
  Proof.
    revert n m. induction l; auto with arith.
    intros n m H. cbn. now apply IHl, Nat.max_le_compat_r.
  Qed.

  Lemma fold_max_inc l b : b <= fold_left max l b.
  Proof.
    induction l; auto.
    cbn. eapply le_trans. now apply IHl. apply fold_max_mono, Nat.le_max_l.
  Qed.

  Lemma all_le l : forall a, In a l -> a <= max_list l.
  Proof.
    induction l as [| b l IH]; intros a; [intros []|intros [E|H]].
    - rewrite E. cbn. apply fold_max_inc.
    - eapply le_trans. now apply IH. cbn. apply fold_max_mono. auto with arith.
  Qed.

  Lemma new_atom_fresh l a : new_atom l <= a -> ~ In a l.
  Proof.
    intros H H'. eapply Nat.nle_succ_diag_l.
    eapply Nat.le_trans; [exact H | now apply all_le].
  Qed.

  Lemma fresh_atom l: {a: atom | ~ In a l}.
  Proof.
    exists (new_atom l). intros H. now eapply new_atom_fresh, H.
  Qed.

End fresh_atom.

(* We can show now that if x has fintite support than we can compute a fresh atom for x. *)
Lemma fin_support_fresh_atom (X: perm_set) A (x: X) : support A x -> {a | a # x}.
Proof.
  intros H. destruct (fresh_atom.fresh_atom A) as [a H'].
  exists a. intros Su. unfold supp in Su. apply H', Su, H.
Qed.
