Require Import
  HoTT.Classes.interfaces.abstract_algebra.

Generalizable Variables A B.

Instance Empty_lt : Lt@{Set Set} Empty.
Proof. intros []. Defined.

Instance Unit_lt : Lt@{Set Set} Unit := fun _ _ => Empty.

Instance empty_tricho : Trichotomy@{Set Set Set} (_:Lt Empty).
Proof.
intros [].
Qed.

Instance unit_tricho : Trichotomy@{Set Set Set} (_:Lt Unit).
Proof.
intros [] [];auto.
Defined.

Section contents.

Context `{Alt : Lt@{Set Set} A} `{Blt : Lt@{Set Set} B}.

#[export] Instance sum_lt : Lt@{Set Set} (A |_| B) | 2
  := fun s1 s2 =>
  match s1, s2 with
  | inl a1, inl a2 => a1 < a2
  | inr b1, inr b2 => b1 < b2
  | inl _, inr _ => Unit
  | inr _, inl _ => Empty
  end.

#[export] Instance sum_tricho `{!Trichotomy@{Set Set Set} Alt} `{!Trichotomy@{Set Set Set} Blt}
  : Trichotomy@{Set Set Set} sum_lt.
Proof.
hnf. intros [a1|b1] [a2|b2];simpl.
- destruct (trichotomy _ a1 a2) as [?|[?|?]];auto.
- auto.
- auto.
- destruct (trichotomy _ b1 b2) as [?|[?|?]];auto.
Defined.

End contents.
