/* build.mjs — src/sub-beam-analyzer.jsx 를 자립형 index.html 로 번들합니다.
   사용법: npm install && npm run build */
import { build } from "esbuild";
import { writeFileSync } from "node:fs";

const entry = `
import React from "react";
import { createRoot } from "react-dom/client";
import App from "./src/sub-beam-analyzer.jsx";
createRoot(document.getElementById("root")).render(React.createElement(App));
`;

const result = await build({
  stdin: { contents: entry, resolveDir: process.cwd(), loader: "jsx" },
  bundle: true,
  minify: true,
  format: "iife",
  define: { "process.env.NODE_ENV": '"production"' },
  charset: "utf8",
  loader: { ".jsx": "jsx" },
  write: false,
  logLevel: "info",
});

const js = result.outputFiles[0].text.replace(/<\/script/gi, "<\\/script");

const html = `<!DOCTYPE html>
<html lang="ko">
<head>
<meta charset="utf-8" />
<meta name="viewport" content="width=device-width, initial-scale=1" />
<title>SUB-BEAM 2D — 연속보·부분골조 해석 (직접강성법)</title>
<meta name="description" content="스팬·기둥·캔틸레버와 등분포/집중/삼각형/부분등분포/사다리꼴 하중을 지원하는 2D 연속보·부분골조 해석 도구. 직접강성법으로 휨모멘트·전단력·처짐을 계산하고 A4 PDF 보고서를 생성합니다." />
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'%3E%3Crect x='2' y='13' width='28' height='5' fill='%231C2B33'/%3E%3Cpath d='M7 18l-5 8h10z' fill='%230F7B8A'/%3E%3Cpath d='M25 18l-5 8h10z' fill='%230F7B8A'/%3E%3C/svg%3E" />
<style>html,body{margin:0;padding:0;background:#F1F3EF}#root{min-height:100vh}</style>
</head>
<body>
<div id="root"></div>
<script>
${js}
</script>
<noscript>이 도구는 JavaScript가 필요합니다. 브라우저에서 JavaScript를 활성화해 주세요.</noscript>
</body>
</html>`;

writeFileSync("index.html", html);
console.log(`index.html 생성 완료 (${(html.length / 1024).toFixed(0)} KB)`);
