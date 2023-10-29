Require Import UniMath.Foundations.All.

Section code.

  Hypothesis U : UU.
  Hypothesis El : U → UU → UU.
  (** [resp] is defined to transport back from the second type of [weq] to the first, 
      contrary to the definition in the paper, in order to match the types of 
      arguments of [weqtransportbUAH]. This reflects in the types of [isisomorphism] 
      and [equality_pair_lemma], where the positions of respective arguments are 
      consequently also flipped. *)
  Hypothesis resp : ∏ a (B C : UU), B ≃ C → El a C → El a B.
  Hypothesis resp_id : ∏ a B (x : El a B), resp a _ _ (idweq B) x = x.

  Definition code : UU := 
    ∑ a : U, 
    ∏ (C : UU), El a C → ∑ P : UU, isaprop P.
  
  Definition instance (c : code) : UU := 
  let (a , P) := c in
    ∑ C : UU, 
    ∑ x : El a C, 
    pr1 (P C x).

  Definition isisomorphism (a : U) {B C}
    (eq : B ≃ C) (x : El a B) (y : El a C) : UU :=
  resp a _ _ eq y = x.

  Definition isomorphic (c : code) (i1 i2 : instance c) : UU :=
  match c, i1, i2 with 
  | (a ,, _), (C ,, x ,, _), (D ,, y ,, _) => ∑ eq : C ≃ D, isisomorphism a eq x y 
  end.

  Definition carrier : ∏ {c}, instance c → UU := λ _ , pr1.

  Definition element : ∏ {c} (X : instance c), El (pr1 c) (carrier X) := λ _ X, pr1 (pr2 X).

  Lemma equality_pair_lemma :
    ∏ c (X Y : instance c),
    (X = Y) ≃
      ∑ eq : carrier X = carrier Y, 
        transportb (El (pr1 c)) eq (element Y) = element X.
  Proof.
    intros.
    unfold instance in X.
    induction X as [C p']. induction p' as [x p].
    induction Y as [D q']. induction q' as [y q].
    apply (weqcomp (weqonpaths (weqtotal2asstol _ (λ x, pr1 (pr2 c (pr1 x) (pr2 x)))) _ _)).
    cbn; unfold weqtotal2asstol, total2asstol; cbn.
    apply (weqcomp (subtypeInjectivity_prop (λ x, pr2 c (pr1 x) (pr2 x)) _ _)).
    apply (weqcomp (total2_paths_equiv _ _ _)).
    unfold "╝". cbn.
    apply weqfibtototal.
    intro eq.
    induction eq. cbn.
    apply weqpathsinv0.
  Defined.

  Theorem isomorphism_is_equality : ∏ c X Y, isomorphic c X Y ≃ X = Y.
  Proof.
    intros.
    induction c as [a P].
    induction X as [C p']. induction p' as [x p].
    induction Y as [D q']. induction q' as [y q].
    unfold isomorphic, isisomorphism.
    assert (Htransport : 
      (∑ eq : C ≃ D, resp a _ _ eq y = x)   ≃
      (∑ eq : C ≃ D, transportb _ (weqtopaths eq) y = x)).
    { apply weqfibtototal.
      intro w.
      rewrite (weqtransportbUAH univalenceAxiom _ _ (resp_id a) ).
      apply idweq. 
    }
    apply (weqcomp Htransport). clear Htransport.
    assert (Huv : 
      (∑ eq : C ≃ D, transportb _ (weqtopaths eq) y = x) ≃
      (∑ eq : C = D, transportb _ eq y = x)).
    { exact (weqfp (invweq (univalence _ _)) _). }
    apply (weqcomp Huv). clear Huv.
    apply invweq.
    exact (equality_pair_lemma (a ,, P) (C ,, x ,, p) (D ,, y ,, q)).
  Defined.

End code.

Section universe.

  Inductive U : UU :=
  | idx    : U
  | type   : U
  | k      : UU → U
  | arrow  : U → U → U
  | otimes : U → U → U
  | oplus  : U → U → U.

  Notation "a ↣ b" := (arrow a b).
  Notation "a ⊗ b" := (otimes a b).
  Notation "a ⊕ b" := (oplus a b).

  Fixpoint El (u : U) (C : UU) : UU :=
  match u with
  | idx  => C
  | type => UU
  | k a  => a
  | (a ↣ b) => El a C → El b C
  | (a ⊗ b) => El a C × El b C
  | (a ⊕ b) => El a C ⨿ El b C
  end.

  (* corresponds to _→-eq_ in the paper *)
  Lemma funiff {A B C D : UU} : A <-> B → C <-> D → (A → C) <-> (B → D).
  Proof.
    intros iffAB iffCD.
    apply make_dirprod.
    - intros ifAC hB.
      apply (pr1 iffCD). apply ifAC. apply (pr2 iffAB). exact hB.
    - intros ifBD hA.
      apply (pr2 iffCD). apply ifBD. apply (pr1 iffAB). exact hA.
  Defined.

  (* corresponds to _×-eq_ in the paper *)
  Lemma andiff {A B C D : UU} : A <-> B → C <-> D → (A × C) <-> (B × D).
  Proof.
    intros iffAB iffCD.
    apply make_dirprod.
    - exact (dirprodf (pr1 iffAB) (pr1 iffCD)).
    - exact (dirprodf (pr2 iffAB) (pr2 iffCD)).
  Defined.

  (* corresponds to _+-eq_ in the paper *)
  Lemma oriff {A B C D : UU} : A <-> B → C <-> D → (A ⨿ C) <-> (B ⨿ D).
  Proof.
    intros iffAB iffCD.
    apply make_dirprod.
    - exact (coprodf (pr1 iffAB) (pr1 iffCD)).
    - exact (coprodf (pr2 iffAB) (pr2 iffCD)).
  Defined.

  Definition cast (a : U) {B C : UU} : B <-> C → El a B <-> El a C.
  Proof.
    intro Hiff.
    induction a as [ | | | b Hb c Hc | b Hb c Hc | b Hb c Hc ].
    - exact Hiff.
    - exact (isrefl_logeq UU).
    - exact (isrefl_logeq u).
    - exact (funiff Hb Hc).
    - exact (andiff Hb Hc).
    - exact (oriff Hb Hc).
  Defined.

  Definition resp {a : U} {B C : UU} : B ≃ C → El a B → El a C.
  Proof.
    intros w ElaB.
    apply (pr1 (cast _ (weq_to_iff w))).
    assumption.
  Defined.

  (* helper lemma used to prove resp_id *)
  Lemma cast_refliff {a : U} {X : UU} : cast a (isrefl_logeq X) = (isrefl_logeq (El a X)).
  Proof.
    induction a.
    - apply idpath.
    - apply idpath.
    - apply idpath.
    - assert (cast_arrow_unfold :
          cast (a1 ↣ a2) (isrefl_logeq X) 
        = funiff (cast a1 (isrefl_logeq X)) (cast a2 (isrefl_logeq X))).
      { apply idpath. }
      rewrite cast_arrow_unfold, IHa1, IHa2. apply idpath.
    - assert (cast_otimes_unfold : 
          cast (a1 ⊗ a2) (isrefl_logeq X) 
        = andiff (cast a1 (isrefl_logeq X)) (cast a2 (isrefl_logeq X))).
      { apply idpath. }
      rewrite cast_otimes_unfold, IHa1, IHa2. apply idpath.
    - assert (cast_oplus_unfold :
          cast (a1 ⊕ a2) (isrefl_logeq X) 
        = oriff (cast a1 (isrefl_logeq X)) (cast a2 (isrefl_logeq X))).
      { apply idpath. }
      rewrite cast_oplus_unfold, IHa1, IHa2.
      unfold oriff, make_dirprod, isrefl_logeq. cbn.
      assert (H : coprodf (idfun _) (idfun _) = idfun (El a1 X ⨿ El a2 X)).
      { unfold coprodf. cbn.
        apply funextsec.
        intro.
        induction x.
        + apply idpath.
        + apply idpath. 
      }
      apply dirprodeq.
      * exact H.
      * exact H.
  Defined.

  Corollary resp_id {a : U} {B : UU} (x : El a B) : resp (idweq B) x = x.
  Proof.
    unfold resp.
    assert (idweq_refliff : weq_to_iff (idweq B) = (isrefl_logeq B)).
    { apply idpath. }
    rewrite idweq_refliff, cast_refliff.
    cbn.
    apply idpath.
  Defined.

End universe.