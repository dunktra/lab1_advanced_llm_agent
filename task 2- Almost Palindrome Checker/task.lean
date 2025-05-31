import Std
open Std

/-- Determines if a string can become a palindrome by removing at most k characters.
    Returns the minimum number of characters to remove, or -1 if impossible with k removals. -/
def almostPalindrome (s : String) (k : Nat) : Int :=
  -- << CODE START >>
  -- First, clean the string by removing non-alphanumeric chars and converting to lowercase
  let cleanedStr := s.toList.filter (fun c => c.isAlphanum) |>.map Char.toLower

  -- Define a helper function to check if a subsequence is a palindrome
  let isPalindrome (list : List Char) : Bool := list == list.reverse

  -- If already a palindrome, return 0
  if isPalindrome cleanedStr then
    0
  -- Almost palindrome: check if removing exactly one character fixes it
  else if (List.range cleanedStr.length).any (fun i =>
    let candidate := cleanedStr.take i ++ cleanedStr.drop (i+1)
    candidate == List.reverse candidate) then
    1
  -- If the string is not a palindrome, run the DP to compute min deletions up to k, returning that number if ≤ k, or –1 if more are needed
  else
    -- Function to compute minimum deletions needed using dynamic programming
    let minDeletionsToMakePalindrome (chars : List Char) : Nat :=
      let n := chars.length

      -- Base case: empty string or single character
      if n <= 1 then
        0
      else
        -- Create a 2D table to store results of subproblems
        -- dp[i][j] = min deletions needed for substring from i to j
        let dp := Id.run do
          let mut dp := Array.replicate n (Array.replicate n 0)

          -- Fill the dp table for all substring lengths
          -- First, handle length 1 (all are palindromes, 0 deletions)
          for i in [0:n] do
            dp := dp.set! i (dp[i]!.set! i 0)

          -- Handle length 2
          for i in [0:n-1] do
            let j := i + 1
            if chars[i]! == chars[j]! then
              dp := dp.set! i (dp[i]!.set! j 0)  -- palindrome like "aa"
            else
              dp := dp.set! i (dp[i]!.set! j 1)  -- need 1 deletion for "ab"

          -- Handle longer substrings
          for len in [3:n+1] do
            for i in [0:n-len+1] do
              let j := i + len - 1

              -- If first and last characters match
              if chars[i]! == chars[j]! then
                dp := dp.set! i (dp[i]!.set! j dp[i+1]![j-1]!)
              else
                -- Try removing first or last character, take minimum
                let removeFirst := dp[i+1]![j]! + 1
                let removeLast := dp[i]![j-1]! + 1
                dp := dp.set! i (dp[i]!.set! j (Nat.min removeFirst removeLast))

          pure dp

        -- Return result for entire string
        dp[0]![n-1]!

    -- Calculate minimum deletions needed
    let minDeletions := minDeletionsToMakePalindrome cleanedStr

    -- Return result based on k constraint
    if minDeletions <= k then
      (minDeletions : Int)
    else
      -1
  -- << CODE END >>

/--
Specification for almostPalindrome function:
1. For a pure palindrome, return 0
2. For a string that can be made palindrome with ≤ k deletions, return the minimum number needed
3. For a string that needs more than k deletions, return -1
-/
def almostPalindrome_spec (s : String) (k : Nat) (result : Int) : Prop :=
  -- << SPEC START >>
  let cleanedStr := s.toList.filter Char.isAlphanum |>.map Char.toLower

  -- Helper function to check if a list is a palindrome
  let isPalindrome (list : List Char) : Bool := list == list.reverse

  -- Helper function to check if by removing elements at the given indices
  -- we get a palindrome
  let isValidRemoval (chars : List Char) (indices : List Nat) : Bool :=
    let remainingChars := chars.zipIdx |>.filter (fun (_, idx) => !indices.contains idx) |>.map (fun (c, _) => c)
    isPalindrome remainingChars

  -- Already a palindrome
  (isPalindrome cleanedStr → result = 0) ∧

  -- Result is between 0 and k (inclusive) or -1
  ((result ≥ 0 ∧ result ≤ k) ∨ result = -1) ∧

  -- If result ≥ 0, there exists a way to remove 'result' characters to make it a palindrome
  (result ≥ 0 →
    ∃ indices : List Nat,
      indices.length = result.toNat ∧
      indices.all (· < cleanedStr.length) ∧
      isValidRemoval cleanedStr indices) ∧

  -- If result ≥ 0, it's the minimum number of removals needed
  (result ≥ 0 →
    ∀ n : Nat, n < result.toNat →
      ¬∃ indices : List Nat,
        indices.length = n ∧
        indices.all (· < cleanedStr.length) ∧
        isValidRemoval cleanedStr indices) ∧

  -- If result = -1, there's no way to remove k or fewer chars to make it a palindrome
  (result = -1 →
    ∀ indices : List Nat,
      indices.length ≤ k →
      indices.all (· < cleanedStr.length) →
      ¬isValidRemoval cleanedStr indices)
  -- << SPEC END >>

-- Actual function evaluation on test cases
#eval almostPalindrome "A man, a plan, a canal: Panama" 3   -- Expected: 0 (already a palindrome)
#eval almostPalindrome "race a car" 3                       -- Expected: 1 (delete the extra middle ‘a’ to get “racecar”)
#eval almostPalindrome "abca" 1                             -- Expected: 1 (delete ‘b’ to get “aca.”)
#eval almostPalindrome "abc" 1                              -- Expected: -1 (need more deletions than allowed)
#eval almostPalindrome "abcde" 2                            -- Expected: -1 (need more deletions than allowed)
#eval almostPalindrome "abcdef" 2                           -- Expected: -1 (need more deletions than allowed)
