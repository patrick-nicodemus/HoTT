Require Import HoTT.Basics HoTT.Types.

(** * Metatheory *)

(** This directory contains files that prove important metatheoretic results about HoTT, but that are not important for internal development of mathematics in HoTT.  Thus, no files in this directory should ever need to be imported by files outside of this directory. *)

(** Many of these results are about ways to prove univalence and function extensionality (which in the main library we simply assert as axioms, though we track their usage with dummy typeclasses).  For convenience, here we define the types of these two statements. *)

Definition Funext_type@{i j} :=
  forall (A : Type@{i}) (P : A -> Type@{j}) f g,
    IsEquiv (@apD10@{i j} A P f g).

(** Univalence is a property of a single universe; its statement lives in a higher universe *)
Definition Univalence_type@{i} : Type@{i+1} :=
  forall (A B : Type@{i}), IsEquiv (equiv_path@{i} A B).
