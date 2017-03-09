package edu.ucla.cs.main;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import edu.ucla.cs.check.UseChecker;
import edu.ucla.cs.mine.FrequentSequenceMiner;
import edu.ucla.cs.mine.LightweightPredicateMiner;
import edu.ucla.cs.mine.SequencePatternMiner;
import edu.ucla.cs.mine.PredicatePatternMiner;
import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.Answer;
import edu.ucla.cs.model.ControlConstruct;
import edu.ucla.cs.model.Violation;
import edu.ucla.cs.model.ViolationType;
import edu.ucla.cs.search.Search;

public class Maple {
	public static void main(String[] args) {
		// 1. find relevant code snippets given one or more APIs
		HashSet<String> apis = new HashSet<String>();
		apis.add("createNewFile");
		Search search = new Search();
		ArrayList<Answer> answers = search.search(apis);
		
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
		SequencePatternMiner pm = new FrequentSequenceMiner(
				"/home/troy/research/BOA/Maple/mining/freq_seq.py",
				"/home/troy/research/BOA/Maple/example/output.txt",
				40, apis);
		HashMap<ArrayList<String>, Integer>  patterns = pm.mine();
		ArrayList<ArrayList<APISeqItem>> composed_patterns = new ArrayList<ArrayList<APISeqItem>>();
		for(ArrayList<String> pattern : patterns.keySet()) {
			// print the sequence patterns
			System.out.println(pattern + ":" + patterns.get(pattern));
			
			PredicatePatternMiner pm2 = new LightweightPredicateMiner(pattern);
			pm2.process();
			HashMap<String, String> predicate_patterns = pm2.find_the_most_common_predicate();
			ArrayList<APISeqItem> p = new ArrayList<APISeqItem>();
			for(String api : pattern) {
				if(api.equals("}")) {
					p.add(ControlConstruct.END_BLOCK);
				} else if (api.equals("TRY {")) {
					p.add(ControlConstruct.TRY);
				} else if (api.equals("IF {")) {
					p.add(ControlConstruct.IF);
				} else if (api.equals("LOOP {")) {
					p.add(ControlConstruct.LOOP);
				} else if (api.equals("CATCH {")) {
					p.add(ControlConstruct.CATCH);
				} else if (api.equals("FINALLY {")) {
					p.add(ControlConstruct.FINALLY);
				} else if (api.equals("ELSE {")){
					p.add(ControlConstruct.ELSE);
				} else {
					String condition;
					if(predicate_patterns.containsKey(api)) {
						condition = predicate_patterns.get(api);
					} else {
						condition = "true";
					}
					p.add(new APICall(api, condition));
				}
			}
			composed_patterns.add(p);
		}
		
		// print composed patterns
		System.out.println("Print API usage patterns composed of sequence patterns and predicate patterns");
		for(ArrayList<APISeqItem> pattern : composed_patterns) {
			System.out.println(pattern);
		}
		
		// pick the longest common pattern
		ArrayList<APISeqItem> lp = new ArrayList<APISeqItem>();
		for(ArrayList<APISeqItem> pattern : composed_patterns) {
			if(lp.size() < pattern.size()) {
				lp = pattern;
			}
		}
		
		// 3. use the patterns to check for the code snippets in the answers
		HashMap<Answer, ArrayList<Violation>> violations = new UseChecker().check(lp, answers);
		int buggy_snippet_count = 0;
		for(Answer a : violations.keySet()) {
			buggy_snippet_count += a.buggy_seq_count;
		}
		System.out.println("Total number of unreliable Java snippets: " + buggy_snippet_count);
		
		for(Answer a : violations.keySet()) {
			System.out.println("Answer Id --- http://stackoverflow.com/questions/" + a.id);
			for(Violation v : violations.get(a)) {
				System.out.println("Violation: " + v.type + ", " + v.item);
			}
		}
		
		// 4. Group violations based on their types
		HashSet<Answer> miss_structure = new HashSet<Answer>();
		HashSet<Answer> disorder_structure = new HashSet<Answer>();
		HashSet<Answer> miss_api = new HashSet<Answer>();
		HashSet<Answer> disorder_api = new HashSet<Answer>();
		HashSet<Answer> wrong_precondition = new HashSet<Answer>();
		for(Answer a : violations.keySet()) {
			System.out.println("Answer Id --- http://stackoverflow.com/questions/" + a.id);
			for(Violation v : violations.get(a)) {
				if(v.type.equals(ViolationType.MissingStructure)) {
					miss_structure.add(a);
				} else if (v.type.equals(ViolationType.DisorderStructure)) {
					disorder_structure.add(a);
				} else if (v.type.equals(ViolationType.MissingMethodCall)) {
					miss_api.add(a);
				} else if (v.type.equals(ViolationType.DisorderMethodCall)) {
					disorder_api.add(a);
				} else if (v.type.equals(ViolationType.IncorrectPrecondition)) {
					wrong_precondition.add(a);
				}
			}
		}
		
		System.out.println("Missing Control-flow Structure: " + miss_structure.size());
		System.out.println("Disorder Control-flow Structure: " + disorder_structure.size());
		System.out.println("Missing API Call: " + miss_api.size());
		System.out.println("Disorder API Call: " + disorder_api.size());
		System.out.println("Incorrect Predicates: " + wrong_precondition.size());
	}
}
