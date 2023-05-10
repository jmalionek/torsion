import snappy
import twistable_revamp as tw
from sage.all import magma, MatrixSpace, Hom
import representation_theory as rep
import time


def exact_torsion_polynomial(manifold, size=40, precision=10000, group_field_info=None, return_iso_time=False):
	"""
	Given a manifold, a precision for the field calculations, and the maximum degree of the
	group field to check, returns the exact holonomy torsion polynomial of the manifold
	"""
	if isinstance(manifold, str):
		M = snappy.manifold(manifold)
	else:
		M = manifold
	entries = M.holonomy_matrix_entries(match_kernel=False)
	if group_field_info is None:
		group_field_info = entries.find_field(precision, size)
	F = group_field_info[0]
	print(F)
	D = M.dirichlet_domain()
	DD = tw.TwistableDomain(D)
	twistyG = DD.dual_fundamental_group()
	simp_iso = twistyG.simplification_isomorphism()
	simpG = simp_iso.codomain()
	magma_simpG = rep.get_magma_group(simpG)
	snappyG = M.fundamental_group()
	magma_snappyG = magma(snappyG)
	length = simpG.ngens()
	tic = time.perf_counter()
	while True:
		try:
			iso = magma.SearchForIsomorphism(magma_simpG, magma_snappyG, length, nvals=3)
			break
		except RuntimeError as e:
			if "Identifier '_sage_' has not been declared or assigned" in e.__str__():
				raise e
			else:
				length += 1
				continue
	toc = time.perf_counter()
	iso_time = toc - tic
	iso, iso_inv = iso[1], iso[2]
	print(iso)
	exact_mat_gens_snappy = get_exact_holonomy_matrices(group_field_info)
	# for rel in snappyG.sage().relations():
	# 	print(rel(*exact_mat_gens_snappy))
	# print('Done printing out the snappy relations')
	# print(exact_mat_gens_snappy)
	Id = exact_mat_gens_snappy[0].parent().identity_matrix()
	exact_mat_gens_simp = []
	for gen in magma_simpG.gens():
		# print(gen)
		# print(iso.Image(gen).Eltseq().sage())
		mat = Id
		for i in iso.Image(gen).Eltseq().sage():
			if i > 0:
				mat = mat * exact_mat_gens_snappy[i - 1]
			else:
				mat = mat * exact_mat_gens_snappy[i.abs() - 1].inverse()
		exact_mat_gens_simp.append(mat)
	# for rel in simpG.relations():
	# 	print(rel(*exact_mat_gens_simp))
	# print('Done printing out the simpG relations')
	# for i, gen in enumerate(exact_mat_gens_snappy):
	# 	print('snappy gen %i' % i)
	# 	print(gen)
	# for i, gen in enumerate(exact_mat_gens_simp):
	# 	print('simp gen %i' % i)
	# 	print(gen)
	exact_mat_gens_twisty = []
	for gen in twistyG.gens():
		exact_mat_gens_twisty.append(simp_iso(gen)(*exact_mat_gens_simp, check=False))
	# for rel in twistyG.relations():
	# 	print(rel(*exact_mat_gens_twisty))
	# print('Done printing out the twisty relations')
	face_mapping = [None] * 2 * len(exact_mat_gens_twisty)
	face_mapping[0::2] = exact_mat_gens_twisty
	face_mapping[1::2] = [mat.inverse() for mat in exact_mat_gens_twisty]
	phi = rep.phi_from_face_mapping(face_mapping, Id)
	poly = DD.exact_torsion_polynomial(phi, F, time_determinant=True, factor_out_monomial=False)
	if return_iso_time:
		return poly, iso_time
	else:
		return poly


def torsion_coefficients_in_trace_field(manifold, return_timings=False):
	"""
	Returns True if every coefficient of the torsion polynomial is an element of the trace field.
	Returns False and the coefficient which is not in the trace field otherwise.
	Additionally, returns the torsion polynomial, trace field, and matrices used for the calculation.
	"""
	if isinstance(manifold, str):
		M = snappy.manifold(manifold)
	else:
		M = manifold
	entries = M.holonomy_matrix_entries(match_kernel=False)
	size = 40
	precision = 10000
	group_field_info = None
	tic = time.perf_counter()
	while group_field_info is None:
		group_field_info = entries.find_field(precision, size)
	toc = time.perf_counter()
	field_time = toc - tic
	group_field = group_field_info[0]
	tic = time.perf_counter()
	poly, iso_time = exact_torsion_polynomial(M, size, precision, return_iso_time=True)
	toc = time.perf_counter()
	torsion_time = toc - tic
	poly_coeffs = poly.coefficients()
	matrices = get_exact_holonomy_matrices(group_field_info)
	# poly_field, new_coeffs, inclusion = group_field.subfield_from_elements(poly_coeffs)
	# print(poly_field)

	n = len(matrices)
	trace_field_gens = set()
	# The trace field is generated by all ordered single, double, and triple products of matrices of increasing index.
	for i in range(n):
		trace_field_gens.add(matrices[i].trace())

	for i in range(n):
		for j in range(i+1, n):
			trace_field_gens.add((matrices[i] * matrices[j]).trace())

	for i in range(n):
		for j in range(i+1, n):
			for k in range(j+1, n):
				mat = matrices[i] * matrices[j] * matrices[k]
				trace_field_gens.add(mat.trace())

	trace_field, traces, inclusion = group_field.subfield_from_elements(trace_field_gens)
	results = {}
	if return_timings:
		results['torsion_time'] = torsion_time
		results['field_time'] = field_time
		results['iso_time'] = iso_time
	results['trace_field'] = trace_field
	results['matrices'] = matrices
	for coeff in poly_coeffs:
		if coeff not in trace_field:
			results['poly_in_trace_field'] = False
			results['bad_coefficient'] = coeff
			return results

	results['poly_in_trace_field'] = True
	return results

def torsion_coefficients_in_invariant_trace_field(manifold, return_timings=False):
	"""
	Returns True if every coefficient of the torsion polynomial is an element of the trace field.
	Returns False and the coefficient which is not in the trace field otherwise.
	Additionally, returns the torsion polynomial, trace field, and matrices used for the calculation.
	"""
	if isinstance(manifold, str):
		M = snappy.manifold(manifold)
	else:
		M = manifold
	entries = M.holonomy_matrix_entries(match_kernel=False)
	size = 40
	precision = 10000
	group_field_info = None
	tic = time.perf_counter()
	while group_field_info is None:
		group_field_info = entries.find_field(precision, size)
	toc = time.perf_counter()
	field_time = toc - tic
	group_field = group_field_info[0]
	tic = time.perf_counter()
	poly, iso_time = exact_torsion_polynomial(M, size, precision, return_iso_time=True)
	toc = time.perf_counter()
	torsion_time = toc - tic
	poly_coeffs = poly.coefficients()
	matrices = get_exact_holonomy_matrices(group_field_info)
	# poly_field, new_coeffs, inclusion = group_field.subfield_from_elements(poly_coeffs)
	# print(poly_field)

	n = len(matrices)
	trace_field_gens = set()
	# The trace field is generated by all ordered single, double, and triple products of matrices of increasing index.
	for i in range(n):
		mat = matrices[i]
		trace_field_gens.add((mat*mat).trace())

	for i in range(n):
		for j in range(i+1, n):
			mat = matrices[i] * matrices[j]
			trace_field_gens.add((mat*mat).trace())

	for i in range(n):
		for j in range(i+1, n):
			for k in range(j+1, n):
				mat = matrices[i] * matrices[j] * matrices[k]
				trace_field_gens.add((mat*mat).trace())

	trace_field, traces, inclusion = group_field.subfield_from_elements(trace_field_gens)
	results = {}
	if return_timings:
		results['torsion_time'] = torsion_time
		results['field_time'] = field_time
		results['iso_time'] = iso_time
	results['trace_field'] = trace_field
	results['matrices'] = matrices
	for coeff in poly_coeffs:
		if coeff not in trace_field:
			results['poly_in_trace_field'] = False
			results['bad_coefficient'] = coeff
			return results

	results['poly_in_trace_field'] = True
	return results



def get_exact_holonomy_matrices(group_field_info):
	"""
	Given the return value from entries.find_field where entries is the return value of
	manifold.holonomy_matrix_entries, this returns the holonomy matrices.
	"""
	F = group_field_info[0]
	entries = group_field_info[2]
	mat_space = MatrixSpace(F, 2)
	assert len(entries) % 4 == 0
	num_mats = len(entries) // 4
	# assert len(entries) // 4 == len(M.fundamental_group().generators())
	exact_matrices = []
	for i in range(num_mats):
		mat = mat_space(group_field_info[2][4 * i:4 * (i + 1)])
		exact_matrices.append(mat)
	return exact_matrices

if __name__ == '__main__':
	# M = snappy.Manifold('K11n34(0,1)')
	# M = snappy.Manifold('K12n1(0,1)')
	M = snappy.OrientableClosedCensus(betti=1)[0]
	# print(M.identify())
	# Did up to 11
	# M = snappy.Manifold('m336(-1, 3)')
	print(torsion_coefficients_in_invariant_trace_field(M, 40))
	# print(exact_torsion_polynomial(M, 80, return_iso_time=True))