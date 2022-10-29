GIT_TOPLEVEL=`git rev-parse --show-toplevel`
export PATH=$GIT_TOPLEVEL/../verilator/bin/:$PATH
export VERILATOR_ROOT=$GIT_TOPLEVEL/../verilator
