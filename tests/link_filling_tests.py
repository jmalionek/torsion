#! /data/keeling/a/nmd/miniconda3/envs/sage_full/bin/sage-python -u
#
#SBATCH --partition m
#SBATCH --tasks=1
#SBATCH --mem-per-cpu=4G
#SBATCH --nice=10000
#SBATCH --time=7-00:00
#SBATCH --array=0-19
#SBATCH --output=/data/keeling/a/jdm7/filled_links/slurm_out_%A_%a
#SBATCH --error=/data/keeling/a/jdm7/slurm_error/filled_links_%a
import time

import snappy
import sys, os
from itertools import product

from sage.all import gcd
sys.path.append('./..')
import twistable_revamp
import pickle
import pandas as pd
import interpolate



def main():
	num_jobs = 20
	task = int(os.environ['SLURM_ARRAY_TASK_ID'])
	num_links = len(snappy.HTLinkExteriors())

	for i in range(task, num_links, num_jobs):
		M = snappy.HTLinkExteriors()[i]
		if M.solution_type(enum = True) > 1:
			continue
		if M.num_cusps() > 2:
			continue
		fillings = []
		if M.num_cusps == 1:
			fillings.append(M.homological_longitude())
		if M.num_cusps == 2:
			n = M.link().linking_number()
			try:
				short_slopes = M.short_slopes(12)
			except:
				continue
			for a1, b1 in short_slopes[0]:
				for a2, b2 in short_slopes[1]:
					if a1*a2 == b1*b2*n**2 and gcd(a1, b1) == gcd(a2, b2) == 1:
						fillings.append([(a1, b1), (a2, b2)])

		for filling in fillings:
			M.dehn_fill(filling)
			name = str(M)
			if f'{name}_output' in os.listdir():
				continue
			M = M.high_precision()
			if M.volume() < .5 or M.solution_type(enum = True) > 3:
				continue
			if M.homology().betti_number() != 1:
				continue
			tic = time.perf_counter()
			upper = norm_in_closed.search_for_small_norm_surface(M)
			poly = interpolate.approximate_polynomial(M, tol = .00000001, method='golden_angle')
			elapsed = time.perf_counter() - tic
			out = {'poly': poly, 'time': elapsed, 'alex': M.alexander_polynomial(), 'upper_bound': upper}
			coeffs = poly.coefficients()
			for j in range(len(coeffs)):
				if (coeffs[j] - coeffs[-j-1]).abs() > .0001:
					print(f'{j} coefficient of manifold {name} not symmetric')
			with open(f'/data/keeling/a/jdm7/filled_links/{name}_output', 'wb') as file:
				pickle.dump(out, file)

if __name__ == '__main__':
	main()