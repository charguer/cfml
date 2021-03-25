source ~/conf/bashrc.sh
dev vo
FILE=`basename \`pwd\``
cq `cat _CoqProjectDev` ${FILE}_proof.v ${FILE}_ml.v &
