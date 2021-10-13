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


def finite_torsions_on_survey_knot(crossings, rep_size, verbose=False):
	"""
		Computes the torsion for the survey knot with the specified crossings, using all representations into PSL_2(F_q)
		where PSL2(F_q) has at most rep_size elements.
	"""
	exterior = knot_sample.exterior(crossings)
	G = exterior.fundamental_group()
	magmaG = magma(G)
	# print(G.sage())
	perm_group_homs = magmaG.SimpleQuotients(rep_size, Family='"PSL2"')
	# print(perm_group_homs)
	# reps = rep_theory.get_representations_through_magma(G.sage(), [2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
	# perm_group_homs = [permutation_groups.magma_permutation_hom_to_sage(perm_group) for perm_group in perm_group_homs[1]]
	pgl_reps = [permutation_groups.magma_permutation_action_to_PGL2(perm_group) for perm_group in perm_group_homs[1]]
	for pgl_rep in pgl_reps:
		rep_theory.check_pgl_rep(pgl_rep, G.sage())
	psl_reps = [rep_theory.lift_PGL2_to_PSL2(pgl_rep) for pgl_rep in pgl_reps]
	sl_reps = [rep_theory.fast_lift_SL2_simple_representation(psl_rep, G.sage()) for psl_rep in psl_reps]
	if verbose:
		print("Finished finding representations")
		print("Found %i representations" % len(sl_reps))
	torsions = []
	reps = []
	for rep in sl_reps:
		if rep is False:
			print('Found representation which could not be lifted to SL2')
		else:
			torsion = tools.compute_torsion(G, bits_prec=100, alpha=snappy_rep_func(rep), symmetry_test=False)
			torsions.append(torsion)
			reps.append(rep)
	return torsions, reps


if __name__ == "__main__":
	for i in range(41, 42):
		print("Working on knot with %i crossings" % i)
		tors, representations = finite_torsions_on_survey_knot(i, 100, verbose=True)
		for tor in tors:
			print(tor)