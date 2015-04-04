##===- projects/sample/tools/sample/Makefile ---------------*- Makefile -*-===##

#
# Indicate where we are relative to the top of the source tree.
#
LEVEL=../..

#
# Give the name of the tool.
#
TOOLNAME=ALIVE

#
# List libraries that we'll need
# We use LIBS because sample is a dynamic library.
#

LINK_COMPONENTS := bitreader bitwriter asmparser irreader instrumentation scalaropts objcarcopts ipo vectorize all-targets
USEDLIBS = alive.a

#
# Include Makefile.common so we know what to do.
#
include $(LEVEL)/Makefile.common

