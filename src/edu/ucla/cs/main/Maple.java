package edu.ucla.cs.main;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import edu.ucla.cs.check.UseChecker;
import edu.ucla.cs.mine.FrequentSequenceMiner;
import edu.ucla.cs.mine.LightweightPredicateMiner;
import edu.ucla.cs.mine.PatternMiner;
import edu.ucla.cs.mine.SequencePatternMiner;
import edu.ucla.cs.mine.PredicatePatternMiner;
import edu.ucla.cs.mine.TraditionalPredicateMiner;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.Answer;
import edu.ucla.cs.model.ControlConstruct;
import edu.ucla.cs.model.Violation;
import edu.ucla.cs.model.ViolationType;
import edu.ucla.cs.search.Search;
import edu.ucla.cs.utils.FileUtils;

public class Maple {
	HashSet<String> types;
	HashSet<HashSet<String>> apis;
	String raw_output;
	String seq;
	double min_support;
	
	public Maple(HashSet<String> types, HashSet<HashSet<String>> apis, String raw_output, String seq, double threshold) {
		this.types = types;
		this.apis = apis;
		this.raw_output = raw_output;
		this.seq = seq;
		this.min_support = threshold;
	}
	
	public void run() {
		// 1. find relevant code snippets given one or more APIs
		Search search = new Search();
		HashSet<Answer> answers = search.search(types, apis);
		
		int count = 0;
		for(Answer answer : answers) {
			count += answer.seq.keySet().size();
		}
		
		System.out.println("Total number of relevant Java snippets: " + count);

		// 2. mine sequence patterns and predicate patterns from Github
		// TODO: currently we assume that we have already retrieved code
		// examples from Github, but later on we need to also do it
		// programatically
		// TODO: we also assume that the raw output from BOA has been
		// pre-processed, e.g., sliced for the lightweight approach, formatted
		// for the traditional approach
		HashMap<ArrayList<APISeqItem>, Integer> patterns = PatternMiner.mine(raw_output, seq, apis, min_support, FileUtils.countLines(seq));
		HashSet<ArrayList<APISeqItem>> set = new HashSet<ArrayList<APISeqItem>>();
		set.addAll(patterns.keySet());
		
		// 3. detect API usage anomalies
		HashMap<Answer, ArrayList<Violation>> violations = Utils.detectAnomaly(
				answers, set);
		
		// 4. classify these API usage anomalies
		Utils.classify(violations);
	}
}
