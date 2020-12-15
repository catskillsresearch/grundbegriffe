import data.nat.basic

#check (by apply_instance : ∀ n, has_bot (set (fin n)))

#check (by apply_instance : ∀ n, has_top (set (fin n)))

#check (by apply_instance : ∀ n, order_bot (set (fin n)))

#check (by apply_instance : ∀ n, order_top (set (fin n)))

#check (by apply_instance : ∀ n, has_sup(set (fin n)))

#check (by apply_instance : ∀ n, has_inf(set (fin n)))

#check (by apply_instance : ∀ n, semilattice_sup(set (fin n)))

#check (by apply_instance : ∀ n, semilattice_inf(set (fin n)))

#check (by apply_instance : ∀ n, lattice(set (fin n)))

#check (by apply_instance : ∀ n, bounded_lattice(set (fin n)))
