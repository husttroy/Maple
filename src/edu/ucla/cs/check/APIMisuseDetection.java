package edu.ucla.cs.main;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.Answer;
import edu.ucla.cs.model.Violation;
import edu.ucla.cs.search.Search;

public class AnomalyDetection {
	HashSet<String> typeQuery;
	HashSet<ArrayList<String>> apiQueries;
	HashSet<ArrayList<APISeqItem>> patterns;
	
	public AnomalyDetection(HashSet<String> typeQuery, HashSet<ArrayList<String>> apiQueries, HashSet<ArrayList<APISeqItem>> patterns) {
		this.typeQuery = typeQuery;
		this.apiQueries = apiQueries;
		this.patterns = patterns;
	}
	
	public void run() {
		// 1. find relevant code snippets given one or more APIs
		Search search = new Search();
		HashSet<Answer> answers = search.search(typeQuery, apiQueries);
		
//		int count = 0;
//		for(Answer answer : answers) {
//			count += answer.seq.keySet().size();
//		}
//		
//		System.out.println("Total number of relevant Java snippets: " + count);
		System.out.println("Total number of relevant Java snippets: " + answers.size());
		
		// detect API usage anomalies
		HashMap<Answer, ArrayList<Violation>> violations = Utils.detectAnomaly(
						answers, patterns);
				
		// 4. classify these API usage anomalies
		Utils.classify(violations);
		
		// 5. count unreliable ones for recognized answers
		int unreliable_recognized = 0;
		for(Answer a : violations.keySet()) {
			if(a.isAccepted || a.score > 0) {
				unreliable_recognized ++;
			}
		}
		int total_recognized = 0;
		int total_score = 0;
		for(Answer a : answers) {
			if(a.isAccepted || a.score > 0) {
				total_recognized ++;
				total_score += a.score;
			}
		}
		
		System.out.println("Total number of recognized snippets: " + total_recognized);
		double avg = ((double) total_score) / total_recognized;
		System.out.println("Average score: " + avg);
		System.out.println("Unreliable recognized snippets: " + unreliable_recognized);
		System.out.println("Total number of unrecognized snippets: " + (answers.size() - total_recognized));
		System.out.println("Unreliable unrecognized snippets: " + (violations.size() - unreliable_recognized));
	}
}
