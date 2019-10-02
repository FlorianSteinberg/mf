From mathcomp Require Import ssreflect ssrfun seq ssrbool.
Require Import mf_set mf.
Require Import Morphisms ProofIrrelevance ChoiceFacts ConstructiveEpsilon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope mf_scope.

Section partial_functions.
  Context (S T:Type).
  Structure partial_function S T :=
    {
      domain: subset S;
      values: {s | s \from domain} -> T;
    }.
  Coercion values: partial_function >-> Funclass.
  Local Notation pf:= partial_function.
  
  Definition PF2MF (f: partial_function S T):=
    make_mf (fun s t =>  exists (P: s\from domain f), f (exist (domain f) s P) = t).

  Definition F2PF (f: S -> T): pf S T.
    by exists (All); case => s _; apply/f/s.
  Defined.
    
  Lemma PF2MF_dom f: domain f === dom (PF2MF f).
  Proof.
    move => s; split => [dm | [t [P]]]//.
    by exists (f (exist (domain f) s dm)); exists dm.
  Qed.

  Lemma PF2MF_sing (f: partial_function S T) : (PF2MF f) \is_singlevalued.
  Proof.
    move => s t t' [P <-] [P' <-].
    by have ->:= proof_irrelevance (s \from domain f) P P'.
  Qed.

  Lemma PF2MF_val (f: partial_function S T) s: f s \from PF2MF f (sval s).
  Proof. by move: s => [s sfd]; exists sfd. Qed.

  Lemma PF2MF_sing_spec (F: S ->> T): FunctionalChoice_on (dom F) T ->
        F \is_singlevalued <-> exists (f: partial_function S T), PF2MF f =~= F.
  Proof.
    move => choice.
    split => [sing | [f <-]]; last exact/PF2MF_sing.
    have /choice [value crct]: forall (s: dom F), exists t, t \from F (sval s) by case.
    exists (Build_partial_function value) => s t; split => [[P <-] | val]; first exact/crct.
    have sfd: s \from dom F by exists t.
    by exists sfd; apply/sing/val/crct.
  Qed.
End partial_functions.
Coercion PF2MF: partial_function >-> multifunction.

Section composition.
  Context (R S T: Type).
  Local Notation pf := partial_function.
  Definition corestriction (g: pf R S) (A: subset S): pf R A.
    exists (make_subset (fun s => {P | g (exist (domain g) s P) \from A})).
    move => [s [P]].
    by exists (g (exist (domain g) s P)).
  Defined.

  Definition partial_composition (f: pf S T) (g: pf R S): pf R T.
    exists (domain (corestriction g (domain f))).
    case => s [sfd gsfd].    
    apply/(f (exist (domain f) (g (exist (domain g) s sfd)) gsfd)).
  Defined.
  Local Notation "f \o_p g" := (partial_composition f g).

  Lemma pcmp_spec f g: f \o_p g =~= f \o g.
  Proof.
    move => s t.
    split => [[[sfd gsfd]] <- | [[gs [[sfd <-] [gsfd <-]]] _]]; last by exists (exist _ sfd gsfd).
    split.
    - exists (g (exist (domain g) s sfd)).
      by split; [exists sfd | exists gsfd].
    move => t' [sfd' <-].
    by rewrite -(proof_irrelevance _ sfd sfd') -PF2MF_dom.
  Qed.
End composition.

Section ssreflect_partial_functions.
  Definition pf2MF S T (f: S -> option T): (S ->> T) :=
    make_mf (fun s => match f s with
	              |	None => empty
	              | Some fs => singleton fs
                      end).
  
  Lemma pf2MF_spec S T (f: S -> option T) s t: t \from pf2MF f s <-> f s = Some t.
  Proof. by split => /=[ | ->]//; case: (f s)=> // _ ->. Qed.

  Definition pf2PF S T (f: S -> option T): partial_function S T.
    exists (make_subset (fun s => f s)); case => s /=.
    by case: (f s) => [t _| ]; first apply/t.
  Defined.

  Lemma pf2PF_spec S T (f: S -> option T): pf2MF f =~= pf2PF f.
  Proof.
    move => s t; split => [/= | [/=sfd <-]]; last by case: (f s) sfd.
    by case E: (f s) => [fs | ]; first by exists.
  Qed.
               
  Lemma pdom_dec S T (f: S -> option T) s: decidable (s \from dom (pf2PF f)).
  Proof.
    by simpl; case E: (f s) => [fs | ]; [left; exists fs; exists | right; case => t []].
  Qed.

  Definition PF2pf S T (f: partial_function S T):
    (forall s, decidable (s \from dom f)) -> S -> option T.
    move => dec s.
    case: (dec s) => [fd | nfd]; last apply/None.
    by apply/Some/f/exist; rewrite PF2MF_dom; apply/fd.
  Defined.
 
  Lemma PF2pf_spec_dep S T (f: partial_function S T) (dec: forall s, decidable (s \from dom f)):
    pf2PF (PF2pf dec) =~= f.
  Proof.
    move => s t.
    split => [/= [] | [sfd <-]]; first by rewrite /PF2pf; case: (dec s) => P //= _ <-; eexists.
    rewrite /= /PF2pf.
    case: (dec s) => [sfd' /=| nfd]; last by exfalso; apply/nfd; rewrite -PF2MF_dom.
    by exists => //=; f_equal; f_equal; apply/proof_irrelevance.
  Qed.

  Lemma PF2pf_spec S T (f: partial_function S T):
    (exists dec: forall s, decidable (s \from dom f), True) <-> exists g, pf2PF g =~= f.
  Proof.
    split => [[dec] | [g eq]]; first by exists (PF2pf dec); apply/PF2pf_spec_dep.
    by exists => // s; case: (pdom_dec g s) => dec; [left | right]; rewrite -eq.
  Qed.

  Global Instance pf2MF_prpr S T: Proper (@eqfun (option T) S ==> @equiv S T) (@pf2MF S T).
  Proof. by move => f g eq s t; rewrite/= eq. Qed.

  Lemma pf2MF_eq S T (f g: S -> option T): f =1 g <-> pf2MF f =~= pf2MF g.
  Proof.
    split => [eq s /= t | eq s].
    - case E: (f s) => [t' | ]//; case E': (g s) => [t''| ]//; try by move: E'; rewrite -eq E.
      by split => <-; apply/Some_inj; rewrite -E' -E eq.
    have /=:= eq s; case E: (f s) => [fs | ]; case E': (g s) => [gs | ] // eq'; first by rewrite (eq' fs).1.  
    - by have []:= (eq' fs).1.
    by have []:= (eq' gs).2.
  Qed.
  
  Lemma F2MF_pf2MF S T (f: S -> T): F2MF f =~= pf2MF (Some \o_f f).
  Proof. done. Qed.

  Local Notation "f '\o_p' g" := (pcomp f g) (at level 50).

  Lemma pf2MF_rcmp_pf2MF R S T (f: S -> option T) (g: R -> option S):
    (pf2MF f) \o_R (pf2MF g) =~= pf2MF (f \o_p g).
  Proof.
    move => r t; split => [[s [/=]] | ].
    - by rewrite /pcomp; case: (g r) => //= _ -> ; case: (f s) => // t' <- .
    by rewrite /pcomp/=; case (g r) => // s; exists s.
  Qed.

  Lemma pf2MF_comp_pf2MF R S T (f: S -> option T) (g: R -> option S):
    (pf2MF f \o pf2MF g) =~= pf2MF (f \o_p g).
  Proof.
    move => r t.
    split.
    - rewrite <- pf2MF_rcmp_pf2MF.
      intros [A _].
      exact A.
    rewrite /pcomp/obind/oapp/=.
    case E: (g r) => [s | ]//.
    case E': (f s) => // eq.
    split; first by exists s; split => //; rewrite E'.
    by move => k /= <-; exists t; rewrite E'.
  Qed.

  Lemma sec_pcncl S T (f: S -> option T) g: (pf2MF f) \o (F2MF g) =~= mf_id <-> pcancel g f.
  Proof.
    split => [sec t | cncl t t']; first by have /=[|[_ [<-]]]//:= (sec t t).2; case E: (f (g t)) => [t'|] // ->.
    rewrite /=; split => [[[_ [<-]]] | <-]; first by rewrite (cncl t).
    by split => [ | _ <- /=]; [exists (g t) | exists t]; rewrite (cncl t).
  Qed.

  Lemma sec_ocncl S T (f: S -> T) g: (F2MF f) \o (pf2MF g) =~= mf_id -> ocancel g f.
  Proof.
    rewrite !F2MF_pf2MF pf2MF_comp_pf2MF.
    have <-: pf2MF (Some \o_f (@id T)) =~= mf_id by trivial.
    rewrite -pf2MF_eq/pcomp/obind/oapp => sec t.
    by have /=:= sec t; case E: (g t) => [s' | ]// => [[<-]].
  Qed.

  Lemma pf2MF_cotot S T (f: S -> option T): f \is_psurjective <-> (pf2MF f) \is_cototal.
  Proof.
    split => sur t; first by have [s eq]:= sur t; exists s; rewrite /= eq.
    by have [s /=]:= sur t; case E: (f s) => // eq; exists s; rewrite -eq.
  Qed.

  Lemma pf2MF_sing S T (f: S -> option T): (pf2MF f) \is_singlevalued.
  Proof. by move => s t t' /=; case: (f s) => //t'' <- <-. Qed.

  Lemma comp_psur R S T (f: R -> option T) (g: S -> option R):
    f \is_psurjective -> g \is_psurjective -> (f \o_p g) \is_psurjective.
  Proof.
    move => /pf2MF_cotot cotot /pf2MF_cotot cotot'.
    by rewrite pf2MF_cotot -pf2MF_comp_pf2MF; apply/comp_cotot/cotot'/cotot/pf2MF_sing.
  Qed.

  Definition partial_functions S T:= make_subset (fun (F: S ->> T) => exists f, pf2MF f =~= F).

  Lemma PF2MF_pexte_PF2MF S T (f g: S -> option T):
    (pf2MF g) \extends (pf2MF f) <-> pextends f g.
  Proof.
    split => exte s t /=; first by move => E; have /=:= exte s t; rewrite E; case: (g s) => // gs ->.
    by case E: (f s) => [fs | ]// <-; case E': (g s) => [gs | ]//; have := exte _ _ E; rewrite E' //; case.
  Qed.

  Lemma ipcf_spec S T (g: S -> option T) f: g \is_partial_choice_for f <->
	                                (pf2MF g) \tightens f.
  Proof.
    split => [ipcf s [t fst] | tight s t fst].
    - by have [t' [/= -> fst']]:= ipcf s t fst; split => [ | _ <-]; first exists t'.
    have [ |[t' /=]]:= tight s; first by exists t.
    by case: (g s) => // _ -> prp; exists t'; split => //; apply prp.
  Qed.

  Lemma pf2MF_fprd S T S' T' (f: S -> option T) (g: S' -> option T'):
    pf2MF (f **_p g) =~= (pf2MF f) ** (pf2MF g).
  Proof.
    move => s [t1 t2]; rewrite /=/pfprd.
    case: (f s.1) => [fs | ]; case: (g s.2) => [gs | ]; try by split; case.
    by split; case => [-> ->].
  Qed.
  
  Lemma pf2MF_fsum S T S' T' (f: S -> option T) (g: S' -> option T'):
    pf2MF (f +s+_p g) =~= (pf2MF f) +s+ (pf2MF g).
  Proof.
    move => s t; rewrite /pfsum /=.
    case: s => [s | s'].
    - case: (f s) => [fs | ]; last by split => //; case: t.
      by case: t => [t | t'] //; split => [[<-] | <-].
    case: (g s') => [gs' | ]; last by split => //; case: t.
    by case: t => [t | t'] //; split => [[<-] | <-].
  Qed.

  Lemma pf2MF_map S T (f: S -> option T): mf_map (pf2MF f) =~= pf2MF (pmap f).
  Proof.
    elim => [[] | s L ih [/= | t K]]//; first by case E: (pmap f L) => [K | ]//; case E': (f s).
    split => [/=[] | /=].
    - by case: (f s) => // _ -> prp; have /= := (ih K).1 prp; case: (pmap f L) => // _ -> .
    case E: (pmap f L) => [K' | ]//.
    by case E': (f s) => [fs | ]// [->  <-]; split; last by apply/ih => /=; rewrite E.
  Qed.

  Lemma pf2MF_comp_F2MF R R' Q (f: R -> R') (g: R' -> option Q):
    (pf2MF g) \o (F2MF f) =~= pf2MF (g \o_f f).
  Proof.
    rewrite F2MF_pf2MF pf2MF_comp_pf2MF -pf2MF_eq => r /=.
    by rewrite /pcomp/obind /=.
  Qed.

  Lemma prd_p_spec R S T (f: R -> option S) (g: R -> option T):
    pf2MF (prd_p f g) =~= prd_mf (pf2MF f) (pf2MF g).
  Proof.
    by rewrite prd_spec -pf2MF_fprd pf2MF_comp_F2MF -pf2MF_eq.
  Qed.

  Lemma PF2MF_lcry R S T (f: S * T -> option R) s:
    pf2MF (lcry_p f s) =~= lcry (pf2MF f) s.
  Proof. done. Qed.
  
  Lemma PF2MF_rcry R S T (f: S * T -> option R) t:
    pf2MF (rcry_p f t) =~= rcry (pf2MF f) t.
  Proof. done. Qed.  
End ssreflect_partial_functions.
Notation "f '\is_partial_function'":= (f \from (partial_functions _ _)) (at level 2): mf_scope.
