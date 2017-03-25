package edu.ucla.cs.search;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.Answer;
import edu.ucla.cs.parse.PartialProgramAnalyzer;

public class Search {
	public HashSet<Answer> search(HashSet<String> typeQuery, HashSet<HashSet<String>> apiQueries) {
		MySQLAccess access = new MySQLAccess();
		access.connect();
		HashSet<HashSet<String>> keywords = new HashSet<HashSet<String>>();
		for(HashSet<String> apiQuery : apiQueries) {
			HashSet<String> keyword = new HashSet<String>();
			keyword.addAll(typeQuery);
			keyword.addAll(apiQuery);
			keywords.add(keyword);
		}
		
		HashSet<Answer> answers = access.searchCodeSnippets(keywords);
		access.close();
		
		Iterator<Answer> iter1 = answers.iterator();
		while(iter1.hasNext()) {
			Answer answer = iter1.next();
			String content = answer.body;
			ArrayList<String> snippets = getCode(content);
			Iterator<String> iter2 = snippets.iterator();
			boolean flag1 = false;
			while(iter2.hasNext()) {
				String snippet = iter2.next();
				// coarse-grained filtering by checking whether it is just a single code term
				if(!snippet.contains(System.lineSeparator()) && !snippet.contains(";")) {
					iter2.remove();
					continue;
				}
				
				// coarse-grained filtering by checking whether the snippet contains keywords from one of the queries
				boolean flag2 = true;
				for(HashSet<String> query : keywords) {
					for(String keyword : query) {
						if(!snippet.contains(keyword)) {
							flag2 = false;
							break;
						}
					}
					
					if(flag2) {
						break;
					}
				}
				
				if(!flag2) {
					iter2.remove();
					continue;
				}
				
				// fine-grained filtering by parsing the code snippet to check for ambiguous names
				PartialProgramAnalyzer analyzer;
				ArrayList<APISeqItem> seq = null;
				try {
					analyzer = new PartialProgramAnalyzer(snippet);
					seq = analyzer.retrieveAPICallSequences();
				} catch (Exception e) {
					// parse error
					iter2.remove();
					continue;
				}
				
				if(seq == null) {
					iter2.remove();
					continue;
				} else {
					// check whether the API call sequences contain all queried keywords
					HashSet<String> calls = new HashSet<String>();
					for(APISeqItem item : seq) {
						if(item instanceof APICall) {
							APICall call = (APICall)item;
							calls.add(call.name);
						}
					}
					
					// remove the snippet if it does not contain the APIs in any of the input queries
					boolean flag = false;
					for(HashSet<String> apis : apiQueries) {
						if(calls.containsAll(apis)) {
							flag = true;
							break;
						} 
					}
					
					if(!flag) {
						// the code snippet does not contain all queried keywords, remove it
						iter2.remove();
						continue;
					} else {
						if(!typeQuery.isEmpty()) {
							// additional check on types to handle ambiguous API calls
							HashSet<String> ts = analyzer.retrieveTypes();
							if(!ts.containsAll(typeQuery)) {
								iter2.remove();
								continue;
							} else {
								answer.seq.put(snippet, seq);
								flag1 = true;
							}
						} else {
							answer.seq.put(snippet, seq);
							flag1 = true;
						}
					}
				}
			}
			
			if(!flag1) {
				// no code snippet in the post is satisfied, remove this post
				iter1.remove();
			}
		}
		
		return answers;
	}
	
	private static ArrayList<String> getCode(String body) {
		ArrayList<String> codes = new ArrayList<>();
		String start = "<code>", end = "</code>";
		int s = 0;
		while (true) {
			s = body.indexOf(start, s);
			if (s == -1)
				break;
			s += start.length();
			int e = body.indexOf(end, s);
			if (e == -1)
				break;
			codes.add(body.substring(s, e).trim());
			s = e + end.length();
		}
		return codes;
	}
}
