package edu.ucla.cs.search;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import edu.ucla.cs.model.APICall;
import edu.ucla.cs.model.APISeqItem;
import edu.ucla.cs.model.Answer;
import edu.ucla.cs.parse.PartialProgramAnalyzer;

public class Search {
	public ArrayList<Answer> search(HashSet<String> keywords) {
		MySQLAccess access = new MySQLAccess();
		access.connect();
		ArrayList<Answer> answers = access.searchCodeSnippets(keywords);
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
				
				// coarse-grained filtering by checking whether the snippet contains all keywords
				boolean flag2 = false;
				for(String keyword: keywords) {
					if(!snippet.contains(keyword)) {
						flag2 = true;
						break;
					}
				}
				
				if(flag2) {
					iter2.remove();
					continue;
				}
				
				// fine-grained filtering by parsing the code snippet to check for ambiguous names
				PartialProgramAnalyzer analyzer = new PartialProgramAnalyzer();
				ArrayList<APISeqItem> seq = analyzer.analyze(snippet);
				if(seq == null) {
					iter2.remove();
				} else {
					// check whether the API call sequences contain all queried keywords
					HashSet<String> calls = new HashSet<String>();
					for(APISeqItem item : seq) {
						if(item instanceof APICall) {
							APICall call = (APICall)item;
							calls.add(call.name);
						}
					}
					
					if(calls.containsAll(keywords)) {
						flag1 = true;
						answer.seq.put(snippet, seq);
					} else {
						// the code snippet does not contain all queried keywords, remove it
						iter2.remove();
					}
					
				}
			}
			
			if(!flag1) {
				// no code snippets in the post is satisfied, remove this post
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
