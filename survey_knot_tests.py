import knot_sample
import representation_theory as rep_theory
import snappy.snap.nsagetools as tools
import string
from sage.all import magma, product
import permutation_groups


def snappy_rep_func(matrices):
	"""Given a list of matrices (one for each generator of a prospective group),
	returns a function which takes in strings representing group elements and returns the representaiton
	of that element.
	"""
	ngens = len(matrices)
	gens_with_inv = string.ascii_lowercase[:ngens] + string.ascii_uppercase[:ngens]
	matrices_with_inv = matrices + [mat.inverse() for mat in matrices]
	rep_dict = {gens_with_inv[i]: matrices_with_inv[i] for i in range(ngens*2)}

	def func(g):
		return product([rep_dict[letter] for letter in g])
	return func


for i in range(3, 1000):
	exterior = knot_sample.exterior(i)
	G = exterior.fundamental_group()
	magmaG = magma(G)
	print(G.sage())
	perm_group_homs = magmaG.SimpleQuotients(10000, Family='"PSL2"')
	print(perm_group_homs)
	# reps = rep_theory.get_representations_through_magma(G.sage(), [2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
	# perm_group_homs = [permutation_groups.magma_permutation_hom_to_sage(perm_group) for perm_group in perm_group_homs[1]]
	pgl_reps = [permutation_groups.magma_permutation_action_to_PGL2(perm_group) for perm_group in perm_group_homs[1]]
	for pgl_rep in pgl_reps:
		rep_theory.check_pgl_rep(pgl_rep, G.sage())
	psl_reps = [rep_theory.lift_PGL2_to_PSL2(pgl_rep) for pgl_rep in pgl_reps]
	sl_reps = [rep_theory.fast_lift_SL2_simple_representation(psl_rep, G.sage()) for psl_rep in psl_reps]
	print("Finished finding representations")
	print(len(sl_reps))
	for rep in sl_reps:
		if rep is False:
			print('Found representation which could not be lifted to SL2')
		else:
			alpha = snappy_rep_func(rep)
			print(alpha('a').base_ring().is_exact())
			torsion = tools.compute_torsion(G, bits_prec=100, alpha=snappy_rep_func(rep))
			print(torsion)
		# print(rep)
