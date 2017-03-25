package edu.ucla.cs.evaluate.example;

import java.util.HashSet;

import edu.ucla.cs.main.Maple;

public class CreateNewFile {
	public static void main(String[] args) {
		HashSet<String> types = new HashSet<String>();
		HashSet<HashSet<String>> queries = new HashSet<HashSet<String>>();
		HashSet<String> apis = new HashSet<String>();
		apis.add("createNewFile");
		queries.add(apis);
		String raw_output = "/home/troy/research/BOA/Maple/example/File.createNewFile/small-sequence.txt";
		String seq = "/home/troy/research/BOA/Maple/example/File.createNewFile/small-output.txt";
		int min_support = 41;
		Maple maple = new Maple(types, queries, raw_output, seq, min_support);
		maple.run();
	}
}
