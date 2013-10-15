#!/usr/bin/env python

# override the default reporting of coords

from pylab import *
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.animation as animation
import random
import datetime
import os

def execCmd(cmd):
	os.system(cmd)


TESTCASES = xrange(213)					# Total 213 testcase
REPEAT    = xrange(1)						# Repeat 5 times for each testcase

class Testcase:
	def __init__(self, identify, size, time):
		self.identify = identify
		self.size = size
		self.time = time
	def pp(self):
		print "==== %s ====\nSize: %d\nTime: %0.5f" % (self.identify, self.size, self.time)
	

def main():
	lstTC = []  				# List of testcase result
	for i in TESTCASES:
		for j in REPEAT:
			t1 = datetime.datetime.now()
			execCmd("./leon ./BT/bigTestcase.scala --numvc=%d --filter=MePo >/dev/null" % i)
			t2 = datetime.datetime.now()
			delta = (t2-t1).total_seconds()
			tc = Testcase("%d_%d"%(i, j), i, delta)
			lstTC.append(tc)
			tc.pp()

	# print "AVG\t%s" % (s/TIMES)
	

def randTest():
	fig, ax = subplots()
	lstTC = []

	def update(data):
		(x, y, cl) = data
		plot(x, y, cl)

	def data_gen():
		i = -1
		while True:
			i = i + 1
			print "Test size %d" % i
			t1 = datetime.datetime.now()
			execCmd("./leon ./BT/bigTestcase.scala --numvc=%d --filter=MePo >/dev/null" % i)
			t2 = datetime.datetime.now()
			delta = (t2-t1).total_seconds()
			tc = Testcase("%d"%i, i, delta)
			lstTC.append(tc)
			tc.pp()
			yield (i, delta , 'ro')

	ani = animation.FuncAnimation(fig, update, data_gen, interval=10000)
	plt.show()

if __name__ == '__main__':
	randTest()
	main()
