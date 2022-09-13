#! /data/keeling/a/nmd/miniconda3/envs/sage_full/bin/sage-python -u
#
#SBATCH --partition m
#SBATCH --tasks=1
#SBATCH --mem-per-cpu=4G
#SBATCH --nice=10000
#SBATCH --time=7-00:00
#SBATCH --output=/data/keeling/a/jdm7/survey_knots_out/rel_survey_knot_%A_cr_%a
#SBATCH --error=/data/keeling/a/jdm7/survey_knots_error/rel_survey_knot_%A_cr_%a
#SBATCH --array=42
#SBATCH --exclude=keeling-h26,keeling-h27,keeling-h28,keeling-h29,keeling-f04,keeling-f18



# Undone Indices: 109,115,116,117,121,122,143,145,151,152,153,155,158,160,164,165,169,170,174,181,187,191,193,195
# Relevant indices: 42,91,94,96,109,115,116,117,121,122,124,132,143,145,151,152,153,155,157,158,160,164,165,169,170,174,175,181,187,188,191,193,195,

import sys, os

import knot_sample
import representation_theory as rep_theory
import snappy.snap.nsagetools as tools
import string
from sage.all import magma, product, prime_powers
import permutation_groups
import time
import pickle


def load_finite_torsion_results():
	with open('/home/joseph/Documents/Math/Research/torsion/files/survey_knot_torsions.pickle', 'rb') as poly_file:
		survey_list = pickle.load(poly_file)
	return survey_list


def save_finite_torsion_results(survey_list):
	with open('/home/joseph/Documents/Math/Research/torsion/files/survey_knot_torsions.pickle', 'wb') as poly_file:
		pickle.dump(survey_list, poly_file)


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


def finite_torsions_on_survey_knot(crossings, rep_size, homlimit=None, verbose=False):
	"""
		Computes the torsion for the survey knot with the specified crossings, using all representations into PSL_2(F_q)
		where PSL2(F_q) has at most rep_size elements.
	"""
	exterior = knot_sample.exterior(crossings)
	G = exterior.fundamental_group()
	magmaG = magma(G)
	# print(G.sage())
	tic = time.perf_counter()
	if homlimit is None:
		perm_group_homs = magmaG.SimpleQuotients(rep_size, Family='"PSL2"')
	else:
		perm_group_homs = magmaG.SimpleQuotients(rep_size, Family='"PSL2"', HomLimit=homlimit)
	print(perm_group_homs)
	toc = time.perf_counter()
	rep_time = toc - tic
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
	tic = time.perf_counter()
	for rep in sl_reps:
		if rep is False:
			print('Found representation which could not be lifted to SL2')
		else:
			torsion = tools.compute_torsion(G, bits_prec=100, alpha=snappy_rep_func(rep), symmetry_test=False)
			torsions.append(torsion)
			reps.append(rep)
	toc = time.perf_counter()
	torsion_time = toc - tic
	returns = {"torsions": torsions, "representations": reps}
	returns['knot_index'] = crossings
	returns['rep_size'] = rep_size
	returns["rep_time"] = rep_time
	returns["torsion_time"] = torsion_time
	degrees = [tor.degree() for tor in torsions]
	max_degree = max(degrees)
	max_degree_index = degrees.index(max_degree)
	returns["max_degree"] = max_degree
	returns["max_degree_index"] = max_degree_index
	returns['homlimit'] = homlimit
	return returns


def exceed_alexander_polynomial(crossings, verbose=False):
	"""
		Computes the torsion for the survey knot with the specified crossings, using all representations into PSL_2(F_q)
		where PSL2(F_q) has at most rep_size elements. Continues doing this until it finds a torsion which would give as
		good or better of a genus bound.
	"""
	exterior = knot_sample.exterior(crossings)
	G = exterior.fundamental_group()
	magmaG = magma(G)
	# print(G.sage())
	rep_time = torsion_time = 0
	torsions = []
	reps = []
	max_degree = None
	max_degree_index = None
	for degree in prime_powers(100):
		tic = time.perf_counter()
		perm_group_homs = magmaG.SimpleQuotients(degree+1, degree+1, 1, 10**9, Family='"PSL2"')
		print(perm_group_homs)
		if len(perm_group_homs) > 0:
			toc = time.perf_counter()
			rep_time = toc - tic
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
			tic = time.perf_counter()
			for rep in sl_reps:
				if rep is False:
					print('Found representation which could not be lifted to SL2')
				else:
					torsion = tools.compute_torsion(G, bits_prec=100, alpha=snappy_rep_func(rep), symmetry_test=False)
					torsions.append(torsion)
					reps.append(rep)
			toc = time.perf_counter()
			torsion_time = toc - tic
			degrees = [tor.degree() for tor in torsions]
			max_degree = max(degrees)
			max_degree_index = degrees.index(max_degree)
			if max_degree/2 + 1 >= exterior.alexander_polynomial().degree():
				break
			if max_degree/2 + 1 == exterior.alexander_polynomial().degree() and (torsion_time+rep_time) > 48*60*60:
				break

	returns = {"torsions": torsions, "representations": reps}
	returns['knot_index'] = crossings
	returns["rep_time"] = rep_time
	returns["torsion_time"] = torsion_time

	returns["max_degree"] = max_degree
	returns["max_degree_index"] = max_degree_index
	return returns


def calculate_all_survey_torsions():
	with open('/home/joseph/Documents/Math/Research/torsion/files/survey_knot_torsions.pickle', 'rb') as poly_file:
		survey_list = pickle.load(poly_file)
	index = -1
	for i in range(len(survey_list)):
		entry = survey_list[i]
		if entry is None:
			index = i
			break
	print('starting with knot with crossing number %i' % index)
	try:
		while index <= 1000:
			entry = finite_torsions_on_survey_knot(index, 1000)
			survey_list[index] = entry
			save_finite_torsion_results(survey_list)
			print('Calculated manifold %s' % index)
			index += 1
	except KeyboardInterrupt as e:
		pass
	except RuntimeError as e:
		survey_list[index] = 'error'


def get_survey_info(i, rep_size):
	entry = finite_torsions_on_survey_knot(i, rep_size)
	print(entry)
	return entry


if __name__ == "__main__":
	# THESE TWO LINES SHOULD BE UNCOMMENTED FOR KEELING
	magma.set_server_and_command(command='/data/keeling/a/nmd/bin/magma')
	index = int(os.environ['SLURM_ARRAY_TASK_ID'])

	entry = exceed_alexander_polynomial(index)
	print(entry)
	# directory = '/home/joseph/Documents/Math/Research/torsion/files/'

	# THESE LINES SHOULD BE UNCOMMENTED FOR KEELING
	directory = '/data/keeling/a/jdm7/survey_knots_out/'
	filename = 'survey_knot_output_exceed_%i' % index
	with open(directory+filename, 'wb') as file:
		pickle.dump(entry, file)




	# calculate_all_survey_torsions()
	# for crossing_num in range(10, 42):
	# 	print("Working on knot with %i crossings" % crossing_num)
	# 	dic = finite_torsions_on_survey_knot(crossing_num, 1000, verbose=True)
	# 	for tor in dic['torsions']:
	# 		print(tor)
