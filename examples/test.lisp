(Define => (lambda A Prop
	     (lambda B Prop
	       (forall x A B))))

(Define ~ (lambda A Prop
	    (forall C Prop ((=> A) C))))

(Define impl_self
  (forall A Prop ((=> A) A)))

(Define impl_self_proof
  (lambda A Prop (lambda H A H)))

(Define verif impl_self_proof impl_self)
