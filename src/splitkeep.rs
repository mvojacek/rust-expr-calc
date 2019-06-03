#[derive(Copy, Clone, Debug, PartialEq)]
pub enum SplitType<'a> {
    Match(&'a str),
    Delimiter(&'a str),
}

#[cfg(not(feature = "unstable"))]
pub struct SplitKeepingDelimiter<'a> {
    haystack: &'a str,
    chars: &'a [char],
    start: usize,
    saved: Option<usize>,
}

#[cfg(not(feature = "unstable"))]
impl<'a> Iterator for SplitKeepingDelimiter<'a> {
    type Item = SplitType<'a>;

    fn next(&mut self) -> Option<SplitType<'a>> {
        if self.start == self.haystack.len() {
            return None;
        }

        if let Some(end_of_match) = self.saved.take() {
            let s = &self.haystack[self.start..end_of_match];
            self.start = end_of_match;
            return Some(SplitType::Delimiter(s));
        }

        let tail = &self.haystack[self.start..];

        match tail.find(self.chars) {
            Some(start) => {
                let start = self.start + start;
                let end = start + 1; // Super dangerous! Assume we are only one byte long
                if self.start == start {
                    let s = &self.haystack[start..end];
                    self.start = end;
                    Some(SplitType::Delimiter(s))
                } else {
                    let s = &self.haystack[self.start..start];
                    self.start = start;
                    self.saved = Some(end);
                    Some(SplitType::Match(s))
                }
            }
            None => {
                let s = &self.haystack[self.start..];
                self.start = self.haystack.len();
                Some(SplitType::Match(s))
            }
        }
    }
}

#[cfg(not(feature = "unstable"))]
pub trait SplitKeepingDelimiterExt: ::std::ops::Index<::std::ops::RangeFull, Output=str> {
    fn split_keeping_delimiter<'p>(&'p self, chars: &'p [char]) -> SplitKeepingDelimiter<'p> {
        for c in chars { assert_eq!(c.len_utf8(), 1) }
        SplitKeepingDelimiter { haystack: &self[..], chars, start: 0, saved: None }
    }
}

impl SplitKeepingDelimiterExt for str {}

#[cfg(test)]
mod test {
    use super::SplitKeepingDelimiterExt;

    #[test]
    fn split_with_delimiter() {
        use super::SplitType::*;
        let delims = &[',', ';'][..];
        let items: Vec<_> = "alpha,beta;gamma".split_keeping_delimiter(delims).collect();
        assert_eq!(
            &items,
            &[
                Match("alpha"),
                Delimiter(","),
                Match("beta"),
                Delimiter(";"),
                Match("gamma")
            ]
        );
    }

    #[test]
    fn split_with_delimiter_allows_consecutive_delimiters() {
        use super::SplitType::*;
        let delims = &[',', ';'][..];
        let items: Vec<_> = ",;".split_keeping_delimiter(delims).collect();
        assert_eq!(&items, &[Delimiter(","), Delimiter(";")]);
    }
}
