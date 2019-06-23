(Define => (lambda A Type
	     (lambda B Type
	       (forall x A B))))

(Define impl_self
  (forall A Prop ((=> A) A)))

(Define impl_self_proof
  (lambda A Prop (lambda H A H)))

(Define verif impl_self_proof impl_self)
