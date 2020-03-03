SLF_FILES="SLFPreface.v SLFDirect.v SLFExtra.v SLFSummary.v SLFBasic.v SLFHprop.v SLFHimpl.v SLFRules.v SLFWPsem.v SLFWPgen.v SLFWand.v SLFStruct.v SLFAffine.v"

CFML_FOLDER=~/cfml2/theories
SLF_FOLDER=~/versions/coq-8.9.1/sfdev/slf

##############################################################################
# Compare SLF

for i in ${SLF_FILES} ; do
  echo "=========================${i}=============================="
  diff ${SLF_FOLDER}/${i} ${CFML_FOLDER}/${i}  | sed -e '/^.[[:space:]]From[[:space:]].*$/d'
done
