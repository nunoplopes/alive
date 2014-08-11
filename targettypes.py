from language import *
from parser import parse_llvm, parse_opt_file
from itertools import combinations

VERBOSE = False

def explicit_check_needed(name, pre, src, tgt):

	if VERBOSE:
		print "\nChecking:", name
		print_prog(src)
		print '=>'
		print_prog(tgt)
		print
	
	type_src = getTypeConstraints(src)
	type_tgt = getTypeConstraints(tgt)
	type_pre = pre.getTypeConstraints()
	
	s = SimpleSolver()
	s.add(type_pre)
	s.add(type_src)
	if s.check() != sat:
		print '%s: source does not type check' % name
		return
	
	s.push()
	s.add(type_tgt)
	if s.check() != sat:
		print '%s: source and target do not type check' % name
		return
	s.pop()
	
# 	for k,v in tgt.iteritems():
# 		#print 'testing %s = %s' % (k,v)
# 		if k not in src: 
# 			s.add(v.getTypeConstraints())
# 			continue
# 		
# 		print k, v.getTypeConstraints()
# 		
# 		s.push()
# 		s.add(Not(v.getTypeConstraints()))
# 		if s.check() == sat:
# 			print '%s: insufficient restrictions for %s' % (name, k)
# 			print s.model()
# 			#exit(0)
# 			return
# 		s.pop()
# 		s.add(v.getTypeConstraints())
	

	# get variables occuring in source and target
	both = [(k,v) for k,v in src.iteritems() if k in tgt]
	
	for (k1,v1),(k2,v2) in combinations(both, 2):
		s.push()
		s.add(Not(v1.type == v2.type))
		
		if s.check() == sat:
			s.add(type_tgt)
		
			if s.check() != sat:
				print '%s: Target requires %s type equal %s' % (name,k1,k2)
			elif VERBOSE:
				print '%s: OK==: No relation between %s and %s' % (name,k1,k2)
		elif VERBOSE:
			print "%s: OK==: Source requires %s type equal %s" % (name,k1,k2)
		
		s.pop()

		s.push()
		s.add(v1.type == v2.type)
		
		if s.check() == sat:
			s.add(type_tgt)
		
			if s.check() != sat:
				print '%s: Target requires %s type unequal %s' % (name,k1,k2)
			elif VERBOSE:
				print '%s: OK<>: No relation between %s and %s' % (name,k1,k2)
		elif VERBOSE:
			print "%s: OK<>: Source requires %s type unequal %s" % (name,k1,k2)
		
		s.pop()

	

def check_file(data = None):
	import sys
	if data == None:
		data = sys.stdin.read()

	opts = parse_opt_file(data)

	for opt in opts:
		explicit_check_needed(*opt)

if __name__ == '__main__':
	check_file()