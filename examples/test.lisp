(Define => (lambda A Prop
	     (lambda B Prop
	       (forall x A B))))

(Define conj (lambda A Prop
	     (lambda B Prop
	       (forall C Prop
		       (=> (=> A (=> B C)) C)))))

(Define disj (lambda A Prop
	     (lambda B Prop
	       (forall C Prop
		       (=> (=> A C) (=> (=> B C) C))))))

(Define ~ (lambda A Prop
	    (forall C Prop (=> A C))))

(Define impl_self_prop
  (forall A Prop (=> A A)))

(Define impl_self_body
  (lambda A Prop (lambda H A H)))

(Define impl_self impl_self_body impl_self_prop)
