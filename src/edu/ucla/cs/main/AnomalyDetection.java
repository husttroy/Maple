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
	HashSet<HashSet<String>> apiQueries;
	HashSet<ArrayList<APISeqItem>> patterns;
	
	public AnomalyDetection(HashSet<String> typeQuery, HashSet<HashSet<String>> apiQueries, HashSet<ArrayList<APISeqItem>> patterns) {
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
	}
}
