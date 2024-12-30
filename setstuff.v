Section Set_Stuff.
  (* A generic element *)
  Variable U : Type.

  (* A set is every element that satisfies a given proposition *)
  Definition set := U -> Prop.

  (* An element is in a set if it satisfies the set's proposition *)
  Definition In (A : set) (x : U) : Prop := A x.

  (* If an element is in A or B, it is in Union A B *)
  Inductive Union (A B : set) : set :=
    | Union_introl : forall x:U, In A x -> In (Union A B) x
    | Union_intror : forall x:U, In B x -> In (Union A B) x.

  (* If an element is in A and B it is in Intersect A B *)
  Inductive Intersect (A B : set) : set :=
    Intersec_intro : forall x:U, In A x -> In B x -> In (Intersect A B) x.

  (* A contains B is the proposition that every element in B is in A *)
  Definition Contains (A B : set) : Prop :=
    forall x:U, In B x -> In A x.

  (* Set equality *)
  Definition Set_Eq (A B : set) : Prop :=
    (Contains A B) /\ (Contains B A).

  Notation "x 'sIn' A" := (In A x) (at level 85).
  Notation "A 'cap' B" := (Intersect A B) (at level 80, right associativity).
  Notation "A 'cup' B" := (Union A B) (at level 85, right associativity).
  Notation "A ~= B" := (Set_Eq A B) (at level 100).
  Notation "A 'subsetOf' B" := (Contains B A) (at level 85).

  (* Theorems *)
  Variables A B : set.

  (* Commutativity of set intersection *)
  Lemma intersect_commutative : A cap B ~= B cap A.
  Proof.
    split;
    intro x;
    unfold In;
    intro;
    induction H as [x H0];
    (split; [exact H | exact H0]).
  Qed.

  (* Commutativity of set union *)
  Lemma union_commutative : A cup B ~= B cup A.
  Proof.
    split;
    intro x;
    unfold In;
    intro H;
    induction H;
    [right;exact H | left;exact H | right;exact H | left;exact H].
  Qed.

  Lemma intersect_of_subsets : forall S1 S2 A : set,
    S1 subsetOf A -> S2 subsetOf A -> Contains A (S1 cap S2).
  Proof.
    unfold Contains.
    intros.
    induction H1.
    apply H.
    exact H1.
  Qed.

  (* Assertion that set A endowed with p (addition), m (multiplication),
     and eq (equality) is a field *)
  Record Field (p m : U->U->U) (eq : U->U->Prop) (A : set) : Prop :=
   mkField {
    (* Commutativity of addition *)
    add_commut : forall x y : U, x sIn A -> y sIn A -> eq (p x y) (p y x);
    (* Commutativity of multiplication *)
    mult_commut : forall x y : U, x sIn A -> y sIn A -> eq (m x y) (m y x);
    (* Associativity of addition *)
    add_assoc : forall x y z : U, x sIn A -> y sIn A -> z sIn A ->
      eq (p x (p y z)) (p (p x y) z);
    (* Associativity of multiplication *)
    mult_assoc : forall x y z : U, x sIn A -> y sIn A -> z sIn A ->
      eq (m x (m y z)) (m (m x y) z);
    (* Existence of multiplicative and additive identity,
       existence of multiplicative and additive inverses *)
    identities : exists zero : U, exists one : U,
      (zero sIn A) /\ (one sIn A) /\ (~ eq zero one) /\
      (forall x : U, x sIn A -> eq (p x zero) x) /\
      (forall x : U, x sIn A -> eq (m x one) x) /\
      (forall x : U, x sIn A ->
        exists y : U, (y sIn A) /\ (eq (p x y) zero)) /\
      (forall x : U, x sIn A -> ~(eq x zero) ->
        exists y : U, (y sIn A) /\ (eq (m x y) one));
    (* Distributivitity of addition and multiplication *)
    dist : forall x y z : U, x sIn A -> y sIn A -> z sIn A ->
      eq (m x (p y z)) (p (m x y) (m x z))
  }.


  (* Assertion that V is the vector space over field F *)
  Record VectorSpace (p m plus times : U->U->U) (e eq: U->U->Prop)
    (F V : set) : Prop :=
   mkVectorSpace {
    over_field : Field p m e F;
    (* Closed under vector addition *)
    add_closed :
      forall (x y : U), x sIn V -> y sIn V -> (plus x y) sIn V;
    (* Closed under scalar multiplication *)
    mult_closed :
      forall (c v : U), c sIn F -> v sIn V -> (times c v) sIn V;
    (* Additive identity and inverse *)
    add_id :
      exists zero:U, (zero sIn V) /\
        (forall x:U, x sIn V -> eq (plus zero x) x) /\
        (forall x:U, x sIn V ->
          exists y:U, (y sIn V) /\ eq (plus x y) zero);
    (* Scalar multiplicative identity *)
    mult_id :
      exists one:U, (one sIn F) /\
        (forall x:U, x sIn V -> eq (times one x) x);
    (* Compatibility of scalar and field multiplication *)
    mult_compat :
      forall a b v:U, a sIn F -> b sIn F -> v sIn V ->
        eq (times a (times b v)) (times (m a b) v);
    plus_commut :
      forall u v:U, u sIn V -> v sIn V ->
        eq (plus u v) (plus v u);
    plus_assoc :
      forall u v w:U, u sIn V -> v sIn V -> w sIn V ->
        eq (plus u (plus v w)) (plus (plus u v) w);
    vec_dist :
      forall c u v:U, c sIn F -> u sIn V -> v sIn V ->
        eq (times c (plus u v)) (plus (times c u) (times c v));
    scalar_dist :
      forall a b v:U, a sIn F -> b sIn F -> v sIn V ->
        eq (times (p a b) v) (plus (times a v) (times b v))
   }.

  Definition Subspace (H : set)
      (p m plus times : U->U->U) (e eq: U->U->Prop) (F V : set) : Prop :=
    (Contains V H) /\ (VectorSpace p m plus times e eq F H).


  Variables p m plus times : U->U->U.
  Variables sEq vEq : U->U->Prop.
  Variables V F : set.

  Notation "V 'isVectorSpace'" := (VectorSpace p m plus times sEq vEq F V)
    (at level 85).
  Notation "S 'isSubspaceOf' V" := (Subspace S p m plus times sEq vEq
    F V) (at level 85).

  Lemma intersect_is_subspace : forall (V : set), V isVectorSpace ->
    forall (S1 S2 : set), S1 isSubspaceOf V -> S2 isSubspaceOf V ->
      ((S1 cap S2) isSubspaceOf V).
  Proof.
    intros.
    unfold Subspace.
    split.

    destruct H0; destruct H1.
    apply intersect_of_subsets; [exact H0 | exact H1].

    split.
    destruct H; exact over_field0.

    split.

    destruct H2; destruct H3.
    destruct H0; destruct H6.
    apply add_closed0; [exact H2 | exact H3].

    destruct H2; destruct H3.
    destruct H1; destruct H6.
    apply add_closed0; [exact H4 | exact H5].

    split.

    destruct H3.
    destruct H0; destruct H5.
    apply mult_closed0; [exact H2 | exact H3].

    destruct H3.
    destruct H1; destruct H5.
    apply mult_closed0; [exact H2 | exact H4].

    (* This is tricky--proving a zero exists in H1 intersects H2
       we take the zero of V0 and show that it satisfies this condition *)
    (*destruct H.
    destruct add_id0 as [zero H_zero].
       exists zero.*)
    destruct H0.
    destruct H2.
    destruct add_id0 as [zero H_zero].
    exists zero.
    split; split.
    destruct H_zero.
    exact H2.

    (* I think you may need to impose restrictions on equality (reflexive, commutative, one-to-one)--then you can prove that the zeros in S1 and S2 are equal *)

    destruct over_field0.

    destruct H1.
    destruct H2.
    destruct add_id0 as [zero0 H_zero0].

    destruct H0; destruct v.
    destruct add_id0; destruct a.
    apply i.
    split.
    destruct H0; destruct H2.
    esplit
    apply add_id0.
    split.
  Qed.

End Set_Stuff.

(* TODO: I think you can prove commutativity of addition from the other tratis for vector spaces *)



(*Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Definition surjective {A B} (f : A -> B) :=
  forall b : B, exists a : A, f a = b.

Theorem injective_surjective : forall (f : A -> A), injective f <-> surjective f.
Proof.
  intro.
  split.
  let a : A.
Qed*
