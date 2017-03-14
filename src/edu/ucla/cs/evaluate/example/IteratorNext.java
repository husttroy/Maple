package edu.ucla.cs.evaluate.example;

import java.util.HashSet;

import edu.ucla.cs.main.Maple;

public class IteratorNext {
	public static void main(String[] args) {
		HashSet<String> types = new HashSet<String>();
		types.add("Iterator");
		HashSet<String> apis = new HashSet<String>();
		apis.add("next");
		String raw_output = "/home/troy/research/BOA/Maple/example/Iterator.next/small-sequence.txt";
		String seq = "/home/troy/research/BOA/Maple/example/Iterator.next/small-output.txt";
		int min_support = 262;
		Maple maple = new Maple(types, apis, raw_output, seq, min_support);
		maple.run();
	}
}
