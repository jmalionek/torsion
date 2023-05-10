#! /data/keeling/a/nmd/miniconda3/envs/sage_full/bin/sage-python -u
#
#SBATCH --partition m
#SBATCH --tasks=1
#SBATCH --mem-per-cpu=4G
#SBATCH --nice=10000
#SBATCH --time=7-00:00
#SBATCH --output=/data/keeling/a/jdm7/field_tests/field_test_out_%A_cr_%a
#SBATCH --error=/data/keeling/a/jdm7/field_tests/field_test_err_%A_cr_%a
#SBATCH --array=0-127
#SBATCH --exclude=keeling-h26,keeling-h27,keeling-h28,keeling-h29,keeling-f04,keeling-f18

import sys, os
import exact_holonomy_torsion as exact
import snappy
import pickle
from sage.all import magma


def get_field_info(index):
	M = snappy.OrientableClosedCensus(betti=1)[index]
	results = exact.torsion_coefficients_in_trace_field(M, True)
	results['index'] = index
	return results


if __name__ == "__main__":
	# THESE TWO LINES SHOULD BE UNCOMMENTED FOR KEELING
	magma.set_server_and_command(command='/data/keeling/a/nmd/bin/magma')
	index = int(os.environ['SLURM_ARRAY_TASK_ID'])

	entry = get_field_info(index)
	print(entry)
	# directory = '/home/joseph/Documents/Math/Research/torsion/files/'
	# THESE LINES SHOULD BE UNCOMMENTED FOR KEELING
	directory = '/data/keeling/a/jdm7/field_tests/'
	filename = 'closed_field_test_%i' % index
	with open(directory+filename, 'wb') as file:
		pickle.dump(entry, file)
