Require Import UniMath.Foundations.All.

Section Code.
  Hypothesis U : UU.
  Hypothesis El : U → UU → UU.
  (** [resp] is defined to transport back from the second type of [weq] to the first, 
      unlike the definition in the paper, in order to match the types of arguments 
      of [weqtransportbUAH]. This reflects in the types of [isisomorphism] and 
      [equality_pair_lemma], where the positions of respective arguments are 
      consequently also flipped. *)
  Hypothesis resp : ∏ a (B C : UU), B ≃ C → El a C → El a B.
  Hypothesis resp_id : ∏ a B (x : El a B), resp a _ _ (idweq B) x = x.
  
  Definition respf : ∏ a (X X' : UU), X ≃ X' → El a X → El a X'.
  Proof.
    intros a X X' w x.
    apply (resp a X' X (invweq w) x).
  Defined.

  Definition ua := univalenceAxiom.

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
      rewrite (weqtransportbUAH ua (El a) (resp a) (resp_id a) ).
      apply idweq. 
    }
    apply (weqcomp Htransport). clear Htransport.
    assert (Huv : 
      (∑ eq : C ≃ D, transportb _ (weqtopaths eq) y = x) ≃
      (∑ eq : C = D, transportb _ eq y = x)).
    { exact (weqfp (invweq (univalence _ _)) (λ eq, transportb _ eq y = x)). }
    apply (weqcomp (Huv)). clear Huv.
    apply invweq.
    exact (equality_pair_lemma (a ,, P) (C ,, x ,, p) (D ,, y ,, q)).
  Defined.

End Code.