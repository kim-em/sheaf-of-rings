import Note
import Render
import BlogTheme

open Verso Doc Genre Blog
open SheafArticle

private def checked {α} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)

private def sourceLinks : IO (Std.HashMap String String) := do
  let mut urls := {}
  for file in ← System.FilePath.readDir "../../counterexample" do
    if file.path.extension == some "thy" then
      let lines := (← IO.FS.readFile file.path).splitOn "\n"
      for (line, i) in lines.zipIdx do
        if line.startsWith "theorem " || line.startsWith "corollary " || line.startsWith "lemma " then
          let name := ((line.splitOn " ")[1]!).splitOn ":" |>.head!
          urls := urls.insert name s!"https://github.com/kim-em/sheaf-of-rings/blob/main/counterexample/{file.fileName}#L{i+1}"
  return urls

def main (_ : List String) : IO UInt32 := do
  let doc := %doc Note
  let ctx : Context := { theoremUrls := ← sourceLinks, referenceKeys := collectReferences doc }
  let body ← checked ((partTeX doc).run ctx)
  let title ← checked ((join <$> doc.title.mapM inlineTeX).run ctx)
  let some metadata := doc.metadata | throw (IO.userError "Article metadata missing")
  let style := include_str "article-style.tex"
  let preamble := style.replace "%TITLE%" title |>.replace "%AUTHOR%" (String.intercalate ", " metadata.authors) |>.replace "%DATE%" (s!"{metadata.date.day} {#["January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"][metadata.date.month-1]!} {metadata.date.year}")
  IO.FS.createDirAll "_out"
  IO.FS.writeFile "_out/note.tex" ("% Generated from verso/Note.lean by make -C article. Do not edit.\n" ++ preamble ++ body ++ "\\end{document}\n")
  let (post, _) ← checked (((partBlog doc).run 0).run ctx)
  let post := { post with metadata := some {
    date := metadata.date
    authors := metadata.authors
    categories := [{name := "lean", slug := "lean"}]
  } }
  let index : Part Page := {title := #[.text "blog"], titleString := "blog", metadata := none, content := #[], subParts := #[]}
  let site := Blog.Site.page `home {index with title := #[.text "kim@lean"], titleString := "kim@lean"}
    #[.blog "blog" `blog index #[{id := `Sheaves, contents := post}]]
  blogMain Site.theme site {} ["--output", "_out/html"]
