#!/usr/bin/env bash

usage() {
cat << EOF
Usage: $0 [-r | -h]
Generates links from current directory for usage by Mathematica.

	-r	removes generated links
	-h	displays detailed help
EOF
}

help () {
cat << EOF
This script links the ./StringCode directory to Mathematica's
\$UserBaseDirectory/Applications folder so that it can be found by Get[] and
Needs[]. This is for active development of the StringCode package and does not
copy any files, leaving the user free to manage the codebase in the current
directory with git.
EOF
}

link=1
while getopts ":hr" opt; do
	case $opt in
		"r")
			link=
			;;
		"h")
			usage
			echo
			echo -n "########################################"
			echo "########################################"
			help
			exit 0
			;;
		"?")
			usage
			exit 1
			;;
	esac
done

shift "$(($OPTIND -1))"

if [[ $# -ne 0 ]]; then
	usage
	exit 1
fi

ask() {
	while true ; do
		if [[ -z $3 ]] ; then
			read -r -p "$1 [$2]: " result
		else
			read -r -p "$1 ($3) [$2]: " result
		fi
		if [[ -z $result ]]; then
			ask_result=$2
			return
		fi
		array=$3
		if [[ -z $3 || " ${array[*]} " =~ ${result} ]]; then
			ask_result=$result
			return
		else
			echo "Invalid option: $result"
		fi
	done
}

if [[ ! -d "StringCode" ]]; then
	echo "Run this script in the git directory containing StringCode/."
	exit 1
fi

StringCodeDir="$(pwd)/StringCode"

# in the future, we should symlink to StringCode-dev to prevent conflicts with
# release version. This just requires renaming StringCode.m to init.m and
# similar

ask "OS" "abort" "Mac Linux"
case $ask_result in
	Mac)
		ApplicationsDir=~/Library/Wolfram/Applications
		;;
	Linux)
		ApplicationsDir=~/.Wolfram/Applications
		;;
	abort)
		echo aborted
		exit 0
		;;
esac

if [[ ! -d $ApplicationsDir ]]; then
	echo "Mathematica installation not found; aborted"
	exit 1
fi


if [[ $link ]]; then
	if [[ -d "$ApplicationsDir/StringCode" ]]; then
		echo "StringCode directory already present; not symlinking"
	exit 1
	fi
	ln -s $StringCodeDir $ApplicationsDir
	echo "linked succesfully"
else
	rm $ApplicationsDir/StringCode
fi
