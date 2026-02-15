(* ::Package:: *)

Module[{rootDir, parentDir},
	rootDir = DirectoryName[DirectoryName[$InputFileName]];
	parentDir = DirectoryName[rootDir];
	If[! MemberQ[$Path, parentDir], PrependTo[$Path, parentDir]];
	Get[FileNameJoin[{rootDir, "StringCode.m"}]];
];
