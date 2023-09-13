#! /data/keeling/a/nmd/miniconda3/envs/sage_full/bin/sage-python -u
#
#SBATCH --partition m
#SBATCH --tasks=1
#SBATCH --mem-per-cpu=4G
#SBATCH --nice=10000
#SBATCH --time=7-00:00
#SBATCH --array=0-19
#SBATCH --output=/data/keeling/a/jdm7/slurm_out/filled_cusps_%a
#SBATCH --error=/data/keeling/a/jdm7/slurm_error/filled_cusps_%a
import time

import snappy
import sys, os
from itertools import product

from sage.all import gcd, FreeModule, matrix, ZZ, vector
from snappy.snap.polished_reps import MapToFreeAbelianization
sys.path.append('./..')
import twistable_revamp
import pickle
import pandas as pd
import interpolate
import norm_in_closed



def main():
	census = snappy.OrientableCuspedCensus()

	num_jobs = 20
	task = int(os.environ['SLURM_ARRAY_TASK_ID'])

	num_manifolds = len(census)

	for i in range(task, num_manifolds, num_jobs):
		M = census[i]
		print(M)
		if M.solution_type(enum = True) > 1:
			continue
		G =  M.fundamental_group()
		Ab = MapToFreeAbelianization(G)
		if M.num_cusps() > 2:
			continue
		fillings = []
		if M.num_cusps() == 1:
			fillings.append(M.homological_longitude())
		if M.num_cusps() == 2:
			a1 = Ab(G.meridian(0))
			b1 = Ab(G.longitude(0))
			a2 = Ab(G.meridian(1))
			b2 = Ab(G.longitude(1))
			A1 = matrix(ZZ, [a1, b1])
			A2 = matrix(ZZ, [a2, b2])
			try:
				short_slopes = M.short_slopes(12)
			except:
				continue
			for s1 in short_slopes[0]:
				s1 = vector(ZZ, s1)
				for s2 in short_slopes[1]:
					s2 = vector(ZZ, s2)
					if s1*A1 == s2*A2:
						fillings.append([s1, s2])

		for filling in fillings:
			print(filling)
			M.dehn_fill(filling)
			assert M.homology().betti_number() > 0
			name = str(M)
			if f'{name}_output' in os.listdir():
				continue
			M = M.high_precision()
			if M.solution_type(enum = True) > 1 or M.volume() < .5:
				continue
			if M.homology().betti_number() != 1:
				continue
			# if M.alexander_polynomial().degree() > 1:
			# 	continue
			tic = time.perf_counter()
			upper = norm_in_closed.search_for_small_norm_surface(M)
			poly = interpolate.approximate_polynomial(M, tol = .00000001, method='golden_angle')
			elapsed = time.perf_counter() - tic
			out = {'poly': poly, 'time':elapsed, 'alex': M.alexander_polynomial(), 'upper_bound':upper}
			coeffs = poly.coefficients()
			for j in range(len(coeffs)):
				if (coeffs[j] - coeffs[-j-1]).abs() > .0001:
					print(f'{j} coefficient of manifold {name} not symmetric')
			with open(f'/data/keeling/a/jdm7/filled_cusps/{name}_output_triv_alex', 'wb') as file:
				pickle.dump(out, file)

if __name__ == '__main__':
	main()