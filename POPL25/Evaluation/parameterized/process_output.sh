#!/bin/bash
if [ \( "$#" -eq 0 \) ] ; then
	echo "usage: ${0} <file>"
	exit 1
fi

echo "Name		#G	 postC	  <="
echo "---------------------------------------"
cat $1 | cut -d'&' --output-delimiter="	"  -f1,3,8,9
