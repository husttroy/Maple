package edu.ucla.cs.utils;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.BufferedReader;
import java.io.IOException;

public class FileUtils {
	
	public static String readFileToString(String path){
		String content = "";
		try (BufferedReader br = new BufferedReader(new FileReader(new File(path)))){
			String line = null;
			while((line = br.readLine()) != null) {
				content += line + System.lineSeparator();
			}
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		return content;
	}

}
