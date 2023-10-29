Require Import UniMath.Foundations.All.

Section code.

  Hypothesis U : UU.
  Hypothesis El : U → UU → UU.
  (** [resp] is defined to transport back from the second type of [weq] to the first, 
      as opposed to the definition in the paper, in order to match the types of 
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
    destruct X as [C p']. destruct p' as [x p].
    destruct Y as [D q']. destruct q' as [y q].
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
    destruct c as [a P].
    destruct X as [C p']. destruct p' as [x p].
    destruct Y as [D q']. destruct q' as [y q].
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
        (∑ eq : C = D, transportb _ eq y = x))
      by exact (weqfp (invweq (univalence _ _)) _).
    apply (weqcomp Huv). clear Huv.
    apply invweq.
    exact (equality_pair_lemma (a ,, P) (C ,, x ,, p) (D ,, y ,, q)).
  Defined.

End code.

Section universe.

  Inductive U : UU :=
  | id    : U
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
  | id  => C
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
    - assert (castarrow_unfold :
          cast (a1 ↣ a2) (isrefl_logeq X) 
        = funiff (cast a1 (isrefl_logeq X)) (cast a2 (isrefl_logeq X)))
      by apply idpath.
      rewrite castarrow_unfold, IHa1, IHa2. apply idpath.
    - assert (castotimes_unfold : 
          cast (a1 ⊗ a2) (isrefl_logeq X) 
        = andiff (cast a1 (isrefl_logeq X)) (cast a2 (isrefl_logeq X)))
      by apply idpath.
      rewrite castotimes_unfold, IHa1, IHa2. apply idpath.
    - assert (castoplus_unfold :
          cast (a1 ⊕ a2) (isrefl_logeq X) 
        = oriff (cast a1 (isrefl_logeq X)) (cast a2 (isrefl_logeq X)))
      by apply idpath.
      rewrite castoplus_unfold, IHa1, IHa2.
      unfold oriff, make_dirprod, isrefl_logeq. cbn.
      assert (H : coprodf (idfun _) (idfun _) = idfun (El a1 X ⨿ El a2 X)).
      { unfold coprodf. cbn.
        apply funextsec.
        intro.
        induction x.
        - apply idpath.
        - apply idpath. 
      }
      apply dirprodeq.
      * exact H.
      * exact H.
  Defined.

  Corollary resp_id {a : U} {B : UU} (x : El a B) : resp (idweq B) x = x.
  Proof.
    unfold resp.
    assert (idweq_refliff : weq_to_iff (idweq B) = (isrefl_logeq B))
      by apply idpath.
    rewrite idweq_refliff, cast_refliff.
    cbn.
    apply idpath.
  Defined.

End universe.

Section monoid.

Require Import UniMath.Algebra.All.
  
  Notation "a ↣ b" := (arrow a b).
  Notation "a ⊗ b" := (otimes a b).
  Notation "a ⊕ b" := (oplus a b).

  Definition Code := code U El.
  
  (* monoid signature *)
  Definition monoidsig := (id ↣ (id ↣ id)) ⊗ id.

  (* monoid properties *)
  Definition monoidprops {C : UU} (ope : El monoidsig C) : UU :=
  match ope with (op,, e) => 
    isaset C × isassoc op × isunit op e
  end.
  
  (* proof that monoid properties are propositional *)
  Lemma monoidpropsisaprop {C : UU} (ope : El monoidsig C) : isaprop (monoidprops ope).
  Proof.
    unfold monoidprops.
    destruct ope as [op e].
    cbn in op.
    intros p q.
    set (hC  := (C,, pr1 p) : hSet ).
    set (bop := op : binop hC ).
    apply isapropdirprod.
    - exact (isapropisaset _).
    - apply isapropdirprod.
      * apply (isapropisassoc bop).
      * apply isapropdirprod.
        + apply (isapropislunit bop).
        + apply (isapropisrunit bop).
  Defined.

  (* code of monoids as given in the paper *)
  Definition monoidcode : Code.
  Proof.
    apply (tpair _ monoidsig). 
    intros C ope.
    apply (tpair _ (monoidprops ope)).
    apply (monoidpropsisaprop ope).
  Defined.

  Definition monoidinstance := instance _ _ monoidcode.

  (** translation from monoids as defined in the standard library
      to monoids defined as instances of [monoidcode] *)
  Definition toinstance : monoid → monoidinstance.
  Proof.
    intro m. unfold monoid, setwithbinop in m.
    destruct m as [setop props].
    destruct props as [hassoc unital].
    destruct unital as [e hisunit].
    destruct setop as [Cset op].
    cbn in e.
    use tpair.
    - exact Cset. 
    - cbn. use tpair. 
      * use make_dirprod.
        exact op. exact e.
      * unfold monoidprops. cbn.
        destruct Cset as [C hset]. 
        apply (make_dirprod hset).
        apply (make_dirprod hassoc).
        exact hisunit.
  Defined.
  
  (** translation from monoids defined as instances of [monoidcode] to 
      monoids as defined in the standard library *)
  Definition frominstance : monoidinstance → monoid.
  Proof.
    intro ms. unfold monoidinstance, instance, monoidcode, pr1 in ms.
    destruct ms as [C structure].
    destruct structure as [sig props].
    destruct sig as [op e]. cbn in op, e.
    destruct props as [hset props].
    destruct props as [hassoc hunit].
    use tpair.
    - exact ((C ,, hset),, op).
    - cbn. unfold ismonoidop.
      apply (make_dirprod hassoc).
      exact (e,, hunit).
  Defined.

  (** weak equality between the monoids of the standard 
      library and instances of [monoidcode] *)
  Theorem weqmonoids : monoidinstance ≃ monoid.
  Proof.
    use weq_iso.
    - exact frominstance.
    - exact toinstance.
    - intro m.
      exact (idpath _).
    - intro m.
      exact (idpath _).
  Defined.

  (** consequent equality between the types *)
  Corollary eqmonoids : monoidinstance = monoid.
  Proof.
    apply univalence. exact weqmonoids.
  Defined.

End monoid.