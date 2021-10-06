import random
from itertools import product
import time

import sage
from sage.matrix.matrix_space import MatrixSpace
from sage.rings.finite_rings.all import GF
from sage.all import matrix, vector, magma
from collections import Counter


def equal_matrices(A, B, tol=.0001):
	return (A - B).norm('frob') < tol


def get_zero(A):
	return MatrixSpace(A.base_ring(), A.nrows(), A.ncols())(0)


def is_essentially_zero(A, tol=10**(-8)):
	return equal_matrices(get_zero(A), A, tol)


def get_identity(A):
	return MatrixSpace(A.base_ring(), A.nrows())(1)


def is_essentially_Id(matrix, tol=10**(-8)):
	return equal_matrices(get_identity(matrix), matrix, tol)


def is_plus_or_minus_Id(matrix):
	return is_essentially_Id(matrix) or is_essentially_Id(-matrix)


def is_projective_representation(matrix_list, relators):
	phi = phi_from_face_mapping(matrix_list)
	for relator in relators:
		result = phi(relator)
		if not is_plus_or_minus_Id(result):
			return False
	# print('\n{0} negative identites found'.format(negative_count))
	return True


def is_nonprojective_representation(matrix_list, relators):
	phi = phi_from_face_mapping(matrix_list)
	for relator in relators:
		if not is_essentially_Id(phi(relator)):
			return False
	return True


def is_exact_representation(matrix_list, relators):
	if len(relators) == 0:
		return True
	phi = phi_from_face_mapping(matrix_list)
	for relator in relators:
		if get_identity(matrix_list[0]) != phi(relator):
			return False
	return True


def check_rep(gens, G):
	assert len(gens) == G.ngens()
	sub_dict = {str(G.gens()[i]): gens[i] for i in range(G.ngens())}
	for relator in G.relations():
		identity = get_identity(gens[0])
		thing = relator.substitute(**sub_dict)
		if identity != thing:
			return False
	return True


def lift_projective_SL2C_representation(matrix_list, relators):
	# phi = phi_from_face_mapping(matrix_list)
	assert is_projective_representation(matrix_list, relators)
	num_generators = int(len(matrix_list)/2)
	# base_gen_images = [phi(i+1) for i in range(int(len(matrix_list)/2))]
	pos_signs = product(*([(1, -1)] * num_generators))
	result = None
	total_iters = 2**num_generators
	iter_count = 0
	for signs in pos_signs:
		images = [None]*num_generators*2
		images[0::2] = [s * M for s, M in zip(signs, matrix_list[0::2])]
		images[1::2] = [s * M for s, M in zip(signs, matrix_list[1::2])]
		# print(signs)
		# print([str((images[i]-matrix_list[i]).norm()) for i in range(num_generators*2)])
		# gen_images = [s * M for s, M in zip(signs, base_gen_images)]
		# if not is_projective_representation(images, relators):
		# 	raise Exception('Intermediate non-representation found')
		if is_nonprojective_representation(images, relators):
			print('\nNonprojective representation found')
			result = images
			return result
		iter_count += 1
		print('\r {0:.2f}% of representations checked'.format(100*iter_count/total_iters), end='')

	if result is None:
		raise Exception('No nonprojective representation found')
	assert is_nonprojective_representation(result, relators)
	return result


def fast_lift_SL2C_representation(matrix_list, relators):
	assert is_projective_representation(matrix_list, relators)
	phi = phi_from_face_mapping(matrix_list)
	sign_vector = [0 if is_essentially_Id(phi(rel)) else 1 for rel in relators]
	Z2 = GF(2)
	sign_vector = vector(Z2, sign_vector)
	num_generators = int(len(matrix_list) / 2)
	num_relators = len(relators)
	delta = matrix(Z2, num_relators, num_generators,
			lambda i, j: relators[i].holonomy.count(j+1)-relators[i].holonomy.count(-j-1))
	if sign_vector in delta.column_space():
		z = delta.solve_right(sign_vector)
		new_matrix_list = [None]*num_generators*2
		new_matrix_list[0::2] = [(-1)**(int(z[i]))*matrix_list[2*i] for i in range(num_generators)]
		new_matrix_list[1::2] = [(-1)**(int(z[i]))*matrix_list[2*i+1] for i in range(num_generators)]
		assert is_nonprojective_representation(new_matrix_list, relators)
		return new_matrix_list
	else:
		return False
		# subset = [random.randing(0, 1) for i in range(num_generators)]
		# new_matrix_list = [None] * num_generators * 2
		# # do the whole process again, but seeding with a different random non-projective representation
		# new_matrix_list[0::2] = [(-1) ** subset[i] * matrix_list[2 * i] for i in range(num_generators)]
		# new_matrix_list[1::2] = [(-1) ** subset[i] * matrix_list[2 * i + 1] for i in range(num_generators)]
		# return fast_lift_SL2C_representation(new_matrix_list, relators)


def fast_lift_SL2_simple_representation(matrix_list, group):
	"""
	Given a list of matrices (one for each generator of the group), which are a PSL_2 representation,
	attempts to lift said representation to SL_2. Returns false if no such representation could be found
	"""
	phi = representation_homomorphism_from_generators(matrix_list, group, check=False)
	Id = get_identity(matrix_list[0])
	for rel in group.relations():
		if phi(rel) not in [Id, -Id]:
			print(phi(rel))
			print(phi(rel).determinant())
			raise RuntimeError('Found representation not in PSL2')
		assert phi(rel) in [Id, -Id]
	sign_vector = vector(GF(2),[0 if phi(rel) == Id else 1 for rel in group.relations()])
	num_relators = len(group.relations())
	delta = matrix(GF(2), num_relators, group.ngens())
	for i, rel in enumerate(group.relations()):
		counts = Counter(rel.Tietze())
		for j in range(group.ngens()):
			delta[i, j] = counts.get(j+1, 0) - counts.get(-j-1, 0)
	if sign_vector in delta.column_space():
		z = delta.solve_right(sign_vector)
		return [(-1)**(int(z[i]))*matrix_list[i] for i in range(group.ngens())]
	else:
		return False


# converts a number from 0 to p^4 into a matrix into a 2 by 2 matrix over Zp
def num_to_matrix(num, p):
	mat = matrix(GF(p), 2)
	mat[0, 0] = num % p
	num = num//p
	mat[0, 1] = num % p
	num = num//p
	mat[1, 0] = num % p
	num = num//p
	mat[1, 1] = num % p
	return mat


def num_to_matrix2(num, p):
	assert num < p**3 - p
	Zp = GF(p)
	mat = matrix(Zp, 2)
	if num < p**2 - p:
		mat[1, 1] = num % p
		num = num//p + 1
		mat[1, 0] = -num
		mat[0, 1] = 1/Zp(num)
	else:
		num = num - p**2 + 1
		b = num % p
		mat[0, 1] = b
		num = num//p
		c = num % p
		mat[1, 0] = c
		num = num//p
		a = (num % (p-1)) + 1
		mat[0, 0] = a
		mat[1, 1] = (1 + b * c)/Zp(a)
	assert mat.det() == Zp(1)
	return mat


def get_SL2p_representations(group, p, return_simplified=False):
	simp = group.simplification_isomorphism()
	G = simp.codomain()
	# print(G.gens())
	Zp = GF(p)
	representations = []
	simp_representations = []
	for i in range(p**(4*G.ngens())):
		matrices = []
		for j in range(G.ngens()):
			mat = num_to_matrix(i//(p**(4*j)) % (p**4), p)
			if mat.det() != Zp.one():
				# print("bad matrix:")
				# print(mat)
				break
			else:
				matrices.append(mat)
			# print("matrices so far")
			# print(matrices)
		if len(matrices) < G.ngens():
			continue
		# print(matrices[0])
		# print(matrices[1])
		# print('\n')
		sub_dict = {str(G.gens()[i]): matrices[i] for i in range(G.ngens())}
		# print(sub_dict)
		rep = True
		for relator in G.relations():
			# print(relator.substitute(**sub_dict))
			if relator.substitute(**sub_dict) != matrix.identity(Zp, 2):
				rep = False
				break
		if rep:
			representations.append([simp(gen).substitute(**sub_dict) for gen in group.gens()])
			simp_representations.append(matrices)
	if return_simplified:
		return representations, simp_representations
	else:
		return representations


def representation_homomorphism_from_generators(matrices, group, check=False):
	"""
		Given a finitely presented sage group with n generators and a list of n matrices, returns a python function
		which takes in elements of the group and returns the matrix representing that element.
		Optionally checks to make sure it is indeed a homomorphism.
	"""
	def func(element):
		return substitute_matrices_into_group_element(matrices, element)
	if check:
		for rel in group.relations():
			assert func(rel) == get_identity(matrices[0])
	return func


def substitute_matrices_into_group_element(matrices, element):
	"""
	Given a list of matrices which represent the generators of the group to which the given element belongs,
	returns the representation of that element.
	"""
	G = element.parent()
	assert G.ngens() == len(matrices)
	sub_dict = {str(G.gens()[i]): matrices[i] for i in range(G.ngens())}
	return element.substitute(**sub_dict)


# Given a simplification isomorphism and matrices corresponding to the generators of the simplified group,
# returns a list of the matrices for the generators of the unsimplified group
def unsimplify_generators(simp_gens, iso):
	G = iso.codomain()
	sub_dict = {str(G.gens()[i]): simp_gens[i] for i in range(G.ngens())}
	return [iso(gen).substitute(**sub_dict) for gen in iso.domain().gens()]


# if certify_irr is true, it will certify that every representation returned is irreducible
def get_SL2p_representations2(group, p, return_simplified=False, certify_irr=False, print_progress=True):
	simp = group.simplification_isomorphism()
	G = simp.codomain()
	# print(G.gens())
	Zp = GF(p)
	representations = []
	simp_representations = []
	SL2pSize = p**3-p

	total = (p ** 2 - p) ** 2 * SL2pSize ** (G.ngens() - 2)
	for i in range(total):
		if print_progress:
			print('Checked {0:.2f}% of total representations, found {1} so far'.format(100*i/total, len(representations)),
				end='\r')
		matrices = []
		certified_irr = False
		# Choosing a basis for our representation consisting of an eigenvector from the first and second
		# matrix, we may assume that up to conjugation, the representation has its first two matrices
		# triangular, one upper and one lower.
		# In Z/p, there are p**2-p (upper or lower) triangular matrices with determinant 1.
		Anum = i % (p**2-p)
		Bnum = (i // (p**2-p)) % p**2-p
		A = matrix(Zp, 2)
		a = Zp(Anum % (p-1)) + 1
		A[0, 0] = a
		A[1, 1] = 1/a
		b = (Anum//p) % p-1
		A[0, 1] = b
		matrices.append(A)
		assert A.det() == Zp(1)
		B = matrix(Zp, 2)
		a = Zp(Bnum % (p-1)) + 1
		B[0, 0] = a
		B[1, 1] = 1 / a
		b = (Bnum // p) % p - 1
		B[1, 0] = b
		matrices.append(B)
		assert B.det() == Zp(1)
		if certify_irr and (A*B*A.inverse()*B.inverse()).trace() != Zp(2):
			certified_irr = True
		for j in range(G.ngens()-2):
			mat = num_to_matrix2((i//(SL2pSize**j)) % SL2pSize, p)
			matrices.append(mat)
		sub_dict = {str(G.gens()[i]): matrices[i] for i in range(G.ngens())}
		rep = True
		for relator in G.relations():
			assert len(matrices) == G.ngens()
			# print(relator.substitute(**sub_dict))
			if relator.substitute(**sub_dict) != matrix.identity(Zp, 2):
				rep = False
				break
		if rep:
			if certify_irr:
				if certified_irr:
					print('\nirreducibility certified with the first two matrices')
					representations.append([simp(gen).substitute(**sub_dict) for gen in group.gens()])
					simp_representations.append(matrices)
				else:
					for m in range(G.ngens()):
						for n in range(m, G.ngens()):
							A = matrices[m]
							B = matrices[n]
							if (A*B*A.inverse()*B.inverse()).trace() != Zp(2):
								certified_irr = True
								print('\nirreducibility certified with the following matrices')
								print(A)
								print(B)
								break
						if certified_irr:
							break
					if certified_irr:
						representations.append([simp(gen).substitute(**sub_dict) for gen in group.gens()])
						simp_representations.append(matrices)
	if return_simplified:
		print('\nFound {} total representations'.format(len(representations)))
		return representations, simp_representations
	else:
		print('\nFound {} total representations'.format(len(representations)))
		return representations


def check_pgl_rep(mats, group):
	phi = representation_homomorphism_from_generators(mats, group)
	for rel in group.relations():
		result = phi(rel)
		if not result.is_diagonal():
			for mat in mats:
				print(mat)
			print(group)
			print(mats[0].base_ring())
			print(result)
			raise RuntimeError('PGL representation was not a PGL representation because image of relation not diagonal')
		if result[0, 0] != result:
			print(mats)
			print(group)
			raise RuntimeError('PGL representation was not a PGL representation since diagonal elements did not match')


def lift_PGL2_to_PSL2(mats):
	new_mats = {}
	bad_mats = {}
	F = mats[0].base_ring()
	for i, mat in enumerate(mats):
		if mat.determinant() == 1:
			new_mats[i] = mat
		elif mat.determinant().is_square():
			new_mats[i] = mat / mat.det().sqrt()
			print(new_mats[i])
			assert new_mats[i].determinant() in [F.one(), -F.one()]
		else:
			bad_mats[i] = mat
	if len(bad_mats) == 0:
		return new_mats
	else:
		print(bad_mats)
		raise RuntimeError("I guess it's not always the case that you can lift these from PGL to PSL")


def get_representations_through_magma(G, p, exclude_PG=True, return_simplified=False):
	simp_iso = G.simplification_isomorphism()
	simpG = simp_iso.codomain()
	magma_str = get_magma_group_string(simpG)
	magmaG = magma(magma_str)
	tic = time.perf_counter()
	all_quot_types = magma.L2Quotients(magmaG)
	toc = time.perf_counter()
	print("L2Quotients algorithm took %f seconds to run" % (toc - tic))
	print(all_quot_types)
	simp_reps = []
	reps = []
	import collections.abc
	if isinstance(p, int):
		p = [p]
	ps = p
	for p in ps:
		for quot_type in all_quot_types:
			quots = quot_type.SpecifyCharacteristic(p)
			for quot in quots:
				print(quot_type, p, quot)
				# Why does magma not work for this?
				if "infty" not in quot.__repr__():
					matrix_group = magma.GetMatrices(quot)
				else:
					continue
				magma_gens = matrix_group.gens()
				gens = [gen.Matrix().sage() for gen in magma_gens]
				if check_rep(gens, simpG):
					inSL = True
					for gen in gens:
						if gen.det() != gen.base_ring().one():
							inSL = False
							print('FOUND REP WHICH IS NOT IN SL')
					simp_reps.append(gens)
					reps.append(unsimplify_generators(gens, simp_iso))
				else:
					print('found a rep which was not in GL2')
					# print('Non-projective representation from Magma, attempting to lift')
					# result = fast_lift_SL2C_representation(gens, relations)
					# if result is False:
					# 	print('Could not lift')
					# else:
					# 	simp_reps.append(result)
					# 	simp_reps.append(unsimplify_generators(gens, simp_iso))
	if return_simplified:
		return reps, simp_reps
	else:
		return reps


def phi_from_Tietze_mapping(mapping, identity=1):
	def phi(hol):
		if isinstance(hol, int):
			return mapping(hol)
		else:
			out = identity
			for i in hol.holonomy:
				# original
				out = out * mapping(i)
			return out
	return phi


def phi_from_face_mapping(mapping, identity=None):
	if hasattr(mapping, '__getitem__'):
		sample = mapping[0]
	else:
		sample = mapping(0)
	if identity is None:
		if isinstance(sample, sage.structure.element.Matrix):
			identity = matrix.identity(sample.base_ring(), sample.dimensions()[0])

	def t_mapping(i):
		sign = 1 if i < 0 else 0
		i = 2 * (abs(i) - 1) + sign
		if hasattr(mapping, '__getitem__'):
			return mapping[i]
		else:
			return mapping(i)

	return phi_from_Tietze_mapping(t_mapping, identity)


# snappy has the convention that the matrix corresponding to face i is the matrix which maps the opposite face to it.
def phi_from_snappy_face_mapping(mapping, identity=1):
	def t_mapping(i):
		sign = 1 if i < 0 else 0
		i = 2 * (abs(i) - 1) + sign
		if i % 2 == 0:
			i += 1
		else:
			i -= 1
		if hasattr(mapping, '__getitem__'):
			return mapping[i]
		else:
			return mapping(i)

	return phi_from_Tietze_mapping(t_mapping, identity)


def get_magma_group_string(group):
	string = 'Group<' + ','.join([str(gen) for gen in group.gens()])
	string += '|' + ','.join([str(rel) for rel in group.relations()]) + '>'
	return string


def get_magma_group(group):
	return magma(get_magma_group_string(group))


