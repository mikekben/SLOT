NAME=$( echo $1 | cut -d "," -f 1 )
TIME=$( echo $1 | cut -d "," -f 3 )

./runthrough.sh $NAME $TIME