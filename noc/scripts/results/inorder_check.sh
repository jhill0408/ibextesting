<!DOCTYPE html>
<html class="" lang="en">
<head prefix="og: http://ogp.me/ns#">
<meta charset="utf-8">
<meta content="IE=edge" http-equiv="X-UA-Compatible">
<meta content="object" property="og:type">
<meta content="GitLab" property="og:site_name">
<meta content="src/script/results/inorder_check.sh · fpt_2018 · watcag / bft-deflection" property="og:title">
<meta content="GitLab Community Edition" property="og:description">
<meta content="https://git.uwaterloo.ca/uploads/project/avatar/8984/screenshot11.png" property="og:image">
<meta content="https://git.uwaterloo.ca/watcag/bft-deflection/blob/fpt_2018/src/script/results/inorder_check.sh" property="og:url">
<meta content="summary" property="twitter:card">
<meta content="src/script/results/inorder_check.sh · fpt_2018 · watcag / bft-deflection" property="twitter:title">
<meta content="GitLab Community Edition" property="twitter:description">
<meta content="https://git.uwaterloo.ca/uploads/project/avatar/8984/screenshot11.png" property="twitter:image">

<title>src/script/results/inorder_check.sh · fpt_2018 · watcag / bft-deflection · GitLab</title>
<meta content="GitLab Community Edition" name="description">
<link rel="shortcut icon" type="image/x-icon" href="/assets/favicon-075eba76312e8421991a0c1f89a89ee81678bcde72319dd3e8047e2a47cd3a42.ico" />
<link rel="stylesheet" media="all" href="/assets/application-1ac1c269cd167f5c95a9efc2a9e84a9c3a7af3770be5eb0818b8ffc3bffcbfd6.css" />
<link rel="stylesheet" media="print" href="/assets/print-9c3a1eb4a2f45c9f3d7dd4de03f14c2e6b921e757168b595d7f161bbc320fc05.css" />
<script src="/assets/application-613cdb2d825326c708f31f460a1faf3e97363027c8ca206fa3b4c13f7d80230c.js"></script>
<meta name="csrf-param" content="authenticity_token" />
<meta name="csrf-token" content="rme4JQVhkDEdbEQd7IUnRtNC1J5ZoV0DQ23vCwMxEdIM2CMiiNJkbp7QF9ww5zmQCY0cBdvg53/wyCLv+mZ8TQ==" />
<meta content="origin-when-cross-origin" name="referrer">
<meta content="width=device-width, initial-scale=1, maximum-scale=1" name="viewport">
<meta content="#474D57" name="theme-color">
<link rel="apple-touch-icon" type="image/x-icon" href="/assets/touch-icon-iphone-5a9cee0e8a51212e70b90c87c12f382c428870c0ff67d1eb034d884b78d2dae7.png" />
<link rel="apple-touch-icon" type="image/x-icon" href="/assets/touch-icon-ipad-a6eec6aeb9da138e507593b464fdac213047e49d3093fc30e90d9a995df83ba3.png" sizes="76x76" />
<link rel="apple-touch-icon" type="image/x-icon" href="/assets/touch-icon-iphone-retina-72e2aadf86513a56e050e7f0f2355deaa19cc17ed97bbe5147847f2748e5a3e3.png" sizes="120x120" />
<link rel="apple-touch-icon" type="image/x-icon" href="/assets/touch-icon-ipad-retina-8ebe416f5313483d9c1bc772b5bbe03ecad52a54eba443e5215a22caed2a16a2.png" sizes="152x152" />
<link color="rgb(226, 67, 41)" href="/assets/logo-d36b5212042cebc89b96df4bf6ac24e43db316143e89926c0db839ff694d2de4.svg" rel="mask-icon">
<meta content="/assets/msapplication-tile-1196ec67452f618d39cdd85e2e3a542f76574c071051ae7effbfde01710eb17d.png" name="msapplication-TileImage">
<meta content="#30353E" name="msapplication-TileColor">




</head>

<body class="ui_charcoal" data-group="" data-page="projects:blob:show" data-project="bft-deflection">
<script>
//<![CDATA[
window.gon={};gon.api_version="v3";gon.default_avatar_url="https:\/\/git.uwaterloo.ca\/assets\/no_avatar-849f9c04a3a0d0cea2424ae97b27447dc64a7dbfae83c036c45b403392f0e8ba.png";gon.max_file_size=10;gon.relative_url_root="";gon.shortcuts_path="\/help\/shortcuts";gon.user_color_scheme="white";gon.award_menu_url="\/emojis";gon.katex_css_url="\/assets\/katex-e46cafe9c3fa73920a7c2c063ee8bb0613e0cf85fd96a3aea25f8419c4bfcfba.css";gon.katex_js_url="\/assets\/katex-04bcf56379fcda0ee7c7a63f71d0fc15ffd2e014d017cd9d51fd6554dfccf40a.js";gon.current_user_id=4902;
//]]>
</script>
<script>
  window.project_uploads_path = "/watcag/bft-deflection/uploads";
  window.preview_markdown_path = "/watcag/bft-deflection/preview_markdown";
</script>

<header class="navbar navbar-fixed-top navbar-gitlab with-horizontal-nav">
<a class="sr-only gl-accessibility" href="#content-body" tabindex="1">Skip to content</a>
<div class="container-fluid">
<div class="header-content">
<button aria-label="Toggle global navigation" class="side-nav-toggle" type="button">
<span class="sr-only">Toggle navigation</span>
<i class="fa fa-bars"></i>
</button>
<button class="navbar-toggle" type="button">
<span class="sr-only">Toggle navigation</span>
<i class="fa fa-ellipsis-v"></i>
</button>
<div class="navbar-collapse collapse">
<ul class="nav navbar-nav">
<li class="hidden-sm hidden-xs">
<div class="has-location-badge search search-form">
<form class="navbar-form" action="/search" accept-charset="UTF-8" method="get"><input name="utf8" type="hidden" value="&#x2713;" /><div class="search-input-container">
<div class="location-badge">This project</div>
<div class="search-input-wrap">
<div class="dropdown" data-url="/search/autocomplete">
<input type="search" name="search" id="search" placeholder="Search" class="search-input dropdown-menu-toggle no-outline js-search-dashboard-options" spellcheck="false" tabindex="1" autocomplete="off" data-toggle="dropdown" data-issues-path="https://git.uwaterloo.ca/dashboard/issues" data-mr-path="https://git.uwaterloo.ca/dashboard/merge_requests" />
<div class="dropdown-menu dropdown-select">
<div class="dropdown-content"><ul>
<li>
<a class="is-focused dropdown-menu-empty-link">
Loading...
</a>
</li>
</ul>
</div><div class="dropdown-loading"><i class="fa fa-spinner fa-spin"></i></div>
</div>
<i class="search-icon"></i>
<i class="clear-icon js-clear-input"></i>
</div>
</div>
</div>
<input type="hidden" name="group_id" id="group_id" class="js-search-group-options" />
<input type="hidden" name="project_id" id="search_project_id" value="8984" class="js-search-project-options" data-project-path="bft-deflection" data-name="bft-deflection" data-issues-path="/watcag/bft-deflection/issues" data-mr-path="/watcag/bft-deflection/merge_requests" />
<input type="hidden" name="search_code" id="search_code" value="true" />
<input type="hidden" name="repository_ref" id="repository_ref" value="fpt_2018" />

<div class="search-autocomplete-opts hide" data-autocomplete-path="/search/autocomplete" data-autocomplete-project-id="8984" data-autocomplete-project-ref="fpt_2018"></div>
</form></div>

</li>
<li class="visible-sm visible-xs">
<a title="Search" aria-label="Search" data-toggle="tooltip" data-placement="bottom" data-container="body" href="/search"><i class="fa fa-search"></i>
</a></li>
<li>
<a title="Todos" aria-label="Todos" data-toggle="tooltip" data-placement="bottom" data-container="body" href="/dashboard/todos"><i class="fa fa-bell fa-fw"></i>
<span class="badge hidden todos-pending-count">
0
</span>
</a></li>
<li class="header-user dropdown">
<a class="header-user-dropdown-toggle" data-toggle="dropdown" href="/gsmalik"><img width="26" height="26" class="header-user-avatar" src="https://secure.gravatar.com/avatar/7161cc90b40dd620b684d53908a6b50b?s=52&amp;d=identicon" alt="7161cc90b40dd620b684d53908a6b50b?s=52&amp;d=identicon" />
<i class="fa fa-caret-down"></i>
</a><div class="dropdown-menu-nav dropdown-menu-align-right">
<ul>
<li>
<a class="profile-link" aria-label="Profile" data-user="gsmalik" href="/gsmalik">Profile</a>
</li>
<li>
<a aria-label="Profile Settings" href="/profile">Profile Settings</a>
</li>
<li>
<a aria-label="Help" href="/help">Help</a>
</li>
<li class="divider"></li>
<li>
<a class="sign-out-link" aria-label="Sign out" rel="nofollow" data-method="delete" href="/users/sign_out">Sign out</a>
</li>
</ul>
</div>
</li>
</ul>
</div>
<h1 class="title"><span><a href="/watcag">watcag</a></span> / <a class="project-item-select-holder" href="/watcag/bft-deflection">bft-deflection</a><button name="button" type="button" class="dropdown-toggle-caret js-projects-dropdown-toggle" aria-label="Toggle switch project dropdown" data-target=".js-dropdown-menu-projects" data-toggle="dropdown"><i class="fa fa-chevron-down"></i></button></h1>
<div class="header-logo">
<a class="home" title="Dashboard" id="logo" href="/"><img src="/uploads/appearance/header_logo/1/uwaterloo-shield.svg" alt="Uwaterloo shield" />
</a></div>
<div class="js-dropdown-menu-projects">
<div class="dropdown-menu dropdown-select dropdown-menu-projects">
<div class="dropdown-title"><span>Go to a project</span><button class="dropdown-title-button dropdown-menu-close" aria-label="Close" type="button"><i class="fa fa-times dropdown-menu-close-icon"></i></button></div>
<div class="dropdown-input"><input type="search" id="" class="dropdown-input-field" placeholder="Search your projects" autocomplete="off" /><i class="fa fa-search dropdown-input-search"></i><i role="button" class="fa fa-times dropdown-input-clear js-dropdown-input-clear"></i></div>
<div class="dropdown-content"></div>
<div class="dropdown-loading"><i class="fa fa-spinner fa-spin"></i></div>
</div>
</div>

</div>
</div>
</header>

<script>
  var findFileURL = "/watcag/bft-deflection/find_file/fpt_2018";
</script>

<div class="page-with-sidebar">
<div class="sidebar-wrapper nicescroll">
<div class="sidebar-action-buttons">
<div class="nav-header-btn toggle-nav-collapse" title="Open/Close">
<span class="sr-only">Toggle navigation</span>
<i class="fa fa-bars"></i>
</div>
<div class="nav-header-btn pin-nav-btn has-tooltip  js-nav-pin" data-container="body" data-placement="right" title="Pin Navigation">
<span class="sr-only">Toggle navigation pinning</span>
<i class="fa fa-fw fa-thumb-tack"></i>
</div>
</div>
<div class="nav-sidebar">
<ul class="nav">
<li class="active home"><a title="Projects" class="dashboard-shortcuts-projects" href="/dashboard/projects"><span>
Projects
</span>
</a></li><li class=""><a class="dashboard-shortcuts-activity" title="Activity" href="/dashboard/activity"><span>
Activity
</span>
</a></li><li class=""><a title="Groups" href="/dashboard/groups"><span>
Groups
</span>
</a></li><li class=""><a title="Milestones" href="/dashboard/milestones"><span>
Milestones
</span>
</a></li><li class=""><a title="Issues" class="dashboard-shortcuts-issues" href="/dashboard/issues?assignee_id=4902"><span>
Issues
<span class="count">0</span>
</span>
</a></li><li class=""><a title="Merge Requests" class="dashboard-shortcuts-merge_requests" href="/dashboard/merge_requests?assignee_id=4902"><span>
Merge Requests
<span class="count">0</span>
</span>
</a></li><li class=""><a title="Snippets" href="/dashboard/snippets"><span>
Snippets
</span>
</a></li></ul>
</div>

</div>
<div class="layout-nav">
<div class="container-fluid">
<div class="controls">
<div class="dropdown project-settings-dropdown">
<a class="dropdown-new btn btn-default" data-toggle="dropdown" href="#" id="project-settings-button">
<i class="fa fa-cog"></i>
<i class="fa fa-caret-down"></i>
</a>
<ul class="dropdown-menu dropdown-menu-align-right">
<li class=""><a title="Members" class="team-tab tab" href="/watcag/bft-deflection/project_members"><span>
Members
</span>
</a></li>
</ul>
</div>
</div>
<div class="nav-control scrolling-tabs-container">
<div class="fade-left">
<i class="fa fa-angle-left"></i>
</div>
<div class="fade-right">
<i class="fa fa-angle-right"></i>
</div>
<ul class="nav-links scrolling-tabs">
<li class="home"><a title="Project" class="shortcuts-project" href="/watcag/bft-deflection"><span>
Project
</span>
</a></li><li class=""><a title="Activity" class="shortcuts-project-activity" href="/watcag/bft-deflection/activity"><span>
Activity
</span>
</a></li><li class="active"><a title="Repository" class="shortcuts-tree" href="/watcag/bft-deflection/tree/fpt_2018"><span>
Repository
</span>
</a></li><li class=""><a title="Pipelines" class="shortcuts-pipelines" href="/watcag/bft-deflection/pipelines"><span>
Pipelines
</span>
</a></li><li class=""><a title="Graphs" class="shortcuts-graphs" href="/watcag/bft-deflection/graphs/fpt_2018"><span>
Graphs
</span>
</a></li><li class=""><a title="Issues" class="shortcuts-issues" href="/watcag/bft-deflection/issues"><span>
Issues
<span class="badge count issue_counter">0</span>
</span>
</a></li><li class=""><a title="Merge Requests" class="shortcuts-merge_requests" href="/watcag/bft-deflection/merge_requests"><span>
Merge Requests
<span class="badge count merge_counter">0</span>
</span>
</a></li><li class=""><a title="Wiki" class="shortcuts-wiki" href="/watcag/bft-deflection/wikis/home"><span>
Wiki
</span>
</a></li><li class="hidden">
<a title="Network" class="shortcuts-network" href="/watcag/bft-deflection/network/fpt_2018">Network
</a></li>
<li class="hidden">
<a class="shortcuts-new-issue" href="/watcag/bft-deflection/issues/new">Create a new issue
</a></li>
<li class="hidden">
<a title="Builds" class="shortcuts-builds" href="/watcag/bft-deflection/builds">Builds
</a></li>
<li class="hidden">
<a title="Commits" class="shortcuts-commits" href="/watcag/bft-deflection/commits/fpt_2018">Commits
</a></li>
<li class="hidden">
<a title="Issue Boards" class="shortcuts-issue-boards" href="/watcag/bft-deflection/boards">Issue Boards</a>
</li>
</ul>
</div>

</div>
</div>
<div class="content-wrapper page-with-layout-nav">
<div class="scrolling-tabs-container sub-nav-scroll">
<div class="fade-left">
<i class="fa fa-angle-left"></i>
</div>
<div class="fade-right">
<i class="fa fa-angle-right"></i>
</div>

<div class="nav-links sub-nav scrolling-tabs">
<ul class="container-fluid container-limited">
<li class="active"><a href="/watcag/bft-deflection/tree/fpt_2018">Files
</a></li><li class=""><a href="/watcag/bft-deflection/commits/fpt_2018">Commits
</a></li><li class=""><a href="/watcag/bft-deflection/network/fpt_2018">Network
</a></li><li class=""><a href="/watcag/bft-deflection/compare?from=master&amp;to=fpt_2018">Compare
</a></li><li class=""><a href="/watcag/bft-deflection/branches">Branches
</a></li><li class=""><a href="/watcag/bft-deflection/tags">Tags
</a></li></ul>
</div>
</div>

<div class="alert-wrapper">


<div class="flash-container flash-container-page">
</div>


</div>
<div class=" ">
<div class="content" id="content-body">

<div class="container-fluid container-limited">

<div class="tree-holder" id="tree-holder">
<div class="nav-block">
<div class="tree-ref-holder">
<form class="project-refs-form" action="/watcag/bft-deflection/refs/switch" accept-charset="UTF-8" method="get"><input name="utf8" type="hidden" value="&#x2713;" /><input type="hidden" name="destination" id="destination" value="blob" />
<input type="hidden" name="path" id="path" value="src/script/results/inorder_check.sh" />
<div class="dropdown">
<button class="dropdown-menu-toggle js-project-refs-dropdown" type="button" data-toggle="dropdown" data-selected="fpt_2018" data-ref="fpt_2018" data-refs-url="/watcag/bft-deflection/refs" data-field-name="ref" data-submit-form-on-click="true"><span class="dropdown-toggle-text ">fpt_2018</span><i class="fa fa-chevron-down"></i></button>
<div class="dropdown-menu dropdown-menu-selectable">
<div class="dropdown-title"><span>Switch branch/tag</span><button class="dropdown-title-button dropdown-menu-close" aria-label="Close" type="button"><i class="fa fa-times dropdown-menu-close-icon"></i></button></div>
<div class="dropdown-input"><input type="search" id="" class="dropdown-input-field" placeholder="Search branches and tags" autocomplete="off" /><i class="fa fa-search dropdown-input-search"></i><i role="button" class="fa fa-times dropdown-input-clear js-dropdown-input-clear"></i></div>
<div class="dropdown-content"></div>
<div class="dropdown-loading"><i class="fa fa-spinner fa-spin"></i></div>
</div>
</div>
</form>
</div>
<ul class="breadcrumb repo-breadcrumb">
<li>
<a href="/watcag/bft-deflection/tree/fpt_2018">bft-deflection
</a></li>
<li>
<a href="/watcag/bft-deflection/tree/fpt_2018/src">src</a>
</li>
<li>
<a href="/watcag/bft-deflection/tree/fpt_2018/src/script">script</a>
</li>
<li>
<a href="/watcag/bft-deflection/tree/fpt_2018/src/script/results">results</a>
</li>
<li>
<a href="/watcag/bft-deflection/blob/fpt_2018/src/script/results/inorder_check.sh"><strong>
inorder_check.sh
</strong>
</a></li>
</ul>
</div>
<ul class="blob-commit-info hidden-xs">
<li class="commit js-toggle-container" id="commit-824497a8">
<a href="/gsmalik"><img class="avatar has-tooltip s36 hidden-xs" alt="Gurshaant Singh Malik&#39;s avatar" title="Gurshaant Singh Malik" data-container="body" src="https://secure.gravatar.com/avatar/7161cc90b40dd620b684d53908a6b50b?s=72&amp;d=identicon" /></a>
<div class="commit-info-block">
<div class="commit-row-title">
<span class="item-title">
<a class="commit-row-message" href="/watcag/bft-deflection/commit/824497a8ac1aadd4e72af391b90f92c97afb5c48">Still fixing results collection</a>
<span class="commit-row-message visible-xs-inline">
&middot;
824497a8
</span>
</span>
<div class="commit-actions hidden-xs">
<button class="btn btn-clipboard btn-transparent" data-toggle="tooltip" data-placement="bottom" data-container="body" data-clipboard-text="824497a8ac1aadd4e72af391b90f92c97afb5c48" type="button" title="Copy to clipboard"><i class="fa fa-clipboard"></i></button>
<a class="commit-short-id btn btn-transparent" href="/watcag/bft-deflection/commit/824497a8ac1aadd4e72af391b90f92c97afb5c48">824497a8</a>

</div>
</div>
<a class="commit-author-link has-tooltip" title="gsmalik@uwaterloo.ca" href="/gsmalik">Gurshaant Singh Malik</a>
committed
<time class="js-timeago" title="Feb 15, 2018 4:47pm" datetime="2018-02-15T21:47:54Z" data-toggle="tooltip" data-placement="top" data-container="body">2018-02-15 16:47:54 -0500</time>
</div>
</li>

</ul>
<div class="blob-content-holder" id="blob-content-holder">
<article class="file-holder">
<div class="file-title">
<i class="fa fa-file-text-o fa-fw"></i>
<strong>
inorder_check.sh
</strong>
<small>
1.31 KB
</small>
<div class="file-actions hidden-xs">
<div class="btn-group tree-btn-group">
<a class="btn btn-sm" target="_blank" href="/watcag/bft-deflection/raw/fpt_2018/src/script/results/inorder_check.sh">Raw</a>
<a class="btn btn-sm" href="/watcag/bft-deflection/blame/fpt_2018/src/script/results/inorder_check.sh">Blame</a>
<a class="btn btn-sm" href="/watcag/bft-deflection/commits/fpt_2018/src/script/results/inorder_check.sh">History</a>
<a class="btn btn-sm" href="/watcag/bft-deflection/blob/6f5a1a7e1156429befc29e5e79f6c0abb6d66c96/src/script/results/inorder_check.sh">Permalink</a>
</div>
<div class="btn-group" role="group">
<a class="btn btn-sm" href="/watcag/bft-deflection/edit/fpt_2018/src/script/results/inorder_check.sh">Edit</a>
<button name="button" type="submit" class="btn btn-default" data-target="#modal-upload-blob" data-toggle="modal">Replace</button>
<button name="button" type="submit" class="btn btn-remove" data-target="#modal-remove-blob" data-toggle="modal">Delete</button>
</div>

</div>
</div>
<div class="file-content code js-syntax-highlight">
<div class="line-numbers">
<a class="diff-line-num" data-line-number="1" href="#L1" id="L1">
<i class="fa fa-link"></i>
1
</a>
<a class="diff-line-num" data-line-number="2" href="#L2" id="L2">
<i class="fa fa-link"></i>
2
</a>
<a class="diff-line-num" data-line-number="3" href="#L3" id="L3">
<i class="fa fa-link"></i>
3
</a>
<a class="diff-line-num" data-line-number="4" href="#L4" id="L4">
<i class="fa fa-link"></i>
4
</a>
<a class="diff-line-num" data-line-number="5" href="#L5" id="L5">
<i class="fa fa-link"></i>
5
</a>
<a class="diff-line-num" data-line-number="6" href="#L6" id="L6">
<i class="fa fa-link"></i>
6
</a>
<a class="diff-line-num" data-line-number="7" href="#L7" id="L7">
<i class="fa fa-link"></i>
7
</a>
<a class="diff-line-num" data-line-number="8" href="#L8" id="L8">
<i class="fa fa-link"></i>
8
</a>
<a class="diff-line-num" data-line-number="9" href="#L9" id="L9">
<i class="fa fa-link"></i>
9
</a>
<a class="diff-line-num" data-line-number="10" href="#L10" id="L10">
<i class="fa fa-link"></i>
10
</a>
<a class="diff-line-num" data-line-number="11" href="#L11" id="L11">
<i class="fa fa-link"></i>
11
</a>
<a class="diff-line-num" data-line-number="12" href="#L12" id="L12">
<i class="fa fa-link"></i>
12
</a>
<a class="diff-line-num" data-line-number="13" href="#L13" id="L13">
<i class="fa fa-link"></i>
13
</a>
<a class="diff-line-num" data-line-number="14" href="#L14" id="L14">
<i class="fa fa-link"></i>
14
</a>
<a class="diff-line-num" data-line-number="15" href="#L15" id="L15">
<i class="fa fa-link"></i>
15
</a>
<a class="diff-line-num" data-line-number="16" href="#L16" id="L16">
<i class="fa fa-link"></i>
16
</a>
<a class="diff-line-num" data-line-number="17" href="#L17" id="L17">
<i class="fa fa-link"></i>
17
</a>
<a class="diff-line-num" data-line-number="18" href="#L18" id="L18">
<i class="fa fa-link"></i>
18
</a>
<a class="diff-line-num" data-line-number="19" href="#L19" id="L19">
<i class="fa fa-link"></i>
19
</a>
<a class="diff-line-num" data-line-number="20" href="#L20" id="L20">
<i class="fa fa-link"></i>
20
</a>
<a class="diff-line-num" data-line-number="21" href="#L21" id="L21">
<i class="fa fa-link"></i>
21
</a>
<a class="diff-line-num" data-line-number="22" href="#L22" id="L22">
<i class="fa fa-link"></i>
22
</a>
<a class="diff-line-num" data-line-number="23" href="#L23" id="L23">
<i class="fa fa-link"></i>
23
</a>
<a class="diff-line-num" data-line-number="24" href="#L24" id="L24">
<i class="fa fa-link"></i>
24
</a>
<a class="diff-line-num" data-line-number="25" href="#L25" id="L25">
<i class="fa fa-link"></i>
25
</a>
<a class="diff-line-num" data-line-number="26" href="#L26" id="L26">
<i class="fa fa-link"></i>
26
</a>
<a class="diff-line-num" data-line-number="27" href="#L27" id="L27">
<i class="fa fa-link"></i>
27
</a>
<a class="diff-line-num" data-line-number="28" href="#L28" id="L28">
<i class="fa fa-link"></i>
28
</a>
<a class="diff-line-num" data-line-number="29" href="#L29" id="L29">
<i class="fa fa-link"></i>
29
</a>
<a class="diff-line-num" data-line-number="30" href="#L30" id="L30">
<i class="fa fa-link"></i>
30
</a>
<a class="diff-line-num" data-line-number="31" href="#L31" id="L31">
<i class="fa fa-link"></i>
31
</a>
<a class="diff-line-num" data-line-number="32" href="#L32" id="L32">
<i class="fa fa-link"></i>
32
</a>
<a class="diff-line-num" data-line-number="33" href="#L33" id="L33">
<i class="fa fa-link"></i>
33
</a>
<a class="diff-line-num" data-line-number="34" href="#L34" id="L34">
<i class="fa fa-link"></i>
34
</a>
<a class="diff-line-num" data-line-number="35" href="#L35" id="L35">
<i class="fa fa-link"></i>
35
</a>
<a class="diff-line-num" data-line-number="36" href="#L36" id="L36">
<i class="fa fa-link"></i>
36
</a>
<a class="diff-line-num" data-line-number="37" href="#L37" id="L37">
<i class="fa fa-link"></i>
37
</a>
</div>
<div class="blob-content" data-blob-id="9c43557429f8c90f0107808e624b751b73847896">
<pre class="code highlight"><code><span id="LC1" class="line"><span class="c">#!/bin/bash</span></span>
<span id="LC2" class="line"><span class="nv">CLIENTS</span><span class="o">=</span><span class="nv">$1</span></span>
<span id="LC3" class="line"><span class="nb">echo</span> <span class="nv">$CLIENTS</span></span>
<span id="LC4" class="line"><span class="nv">N</span><span class="o">=</span><span class="k">$(</span><span class="nb">echo</span> <span class="k">$((</span>CLIENTS-1<span class="k">)))</span></span>
<span id="LC5" class="line"><span class="nb">echo</span> <span class="nv">$N</span></span>
<span id="LC6" class="line"></span>
<span id="LC7" class="line">rm sent_<span class="k">*</span></span>
<span id="LC8" class="line">rm recv_<span class="k">*</span></span>
<span id="LC9" class="line"><span class="k">for </span><span class="nb">source </span><span class="k">in</span> <span class="k">$(</span>seq 0 <span class="nv">$N</span><span class="k">)</span></span>
<span id="LC10" class="line"><span class="k">do</span></span>
<span id="LC11" class="line"><span class="k">	for </span>destination <span class="k">in</span> <span class="k">$(</span>seq 0 <span class="nv">$N</span><span class="k">)</span></span>
<span id="LC12" class="line">	<span class="k">do</span></span>
<span id="LC13" class="line"><span class="k">		if</span> <span class="o">[</span> <span class="nv">$source</span> -ne <span class="nv">$destination</span> <span class="o">]</span></span>
<span id="LC14" class="line">		<span class="k">then</span></span>
<span id="LC15" class="line"><span class="k">			</span>grep <span class="s2">"Sent packet from PE(</span><span class="nv">$source</span><span class="s2">) to PE(</span><span class="nv">$destination</span><span class="s2">)"</span> test.log | awk <span class="s1">'{print $10}'</span> | sed <span class="s2">"s/data=//"</span> &gt; <span class="s2">"sent_</span><span class="nv">$source$destination</span><span class="s2">.log"</span></span>
<span id="LC16" class="line">			<span class="k">while </span><span class="nb">read</span> -r LINE;</span>
<span id="LC17" class="line">			<span class="k">do</span></span>
<span id="LC18" class="line"><span class="c">#				echo $LINE</span></span>
<span id="LC19" class="line">				grep <span class="s2">"Received packet at PE(</span><span class="nv">$destination</span><span class="s2">) with data=</span><span class="nv">$LINE</span><span class="se">\$</span><span class="s2">"</span> test.log | awk <span class="s1">'{print $1 $7}'</span>| sed <span class="s2">"s/Time//"</span> | sed <span class="s2">"s/:data=/</span><span class="se">\ </span><span class="s2">/"</span> &gt;&gt; <span class="s2">"recv_</span><span class="nv">$source$destination</span><span class="s2">.log"</span></span>
<span id="LC20" class="line">			<span class="k">done</span> &lt; <span class="s2">"sent_</span><span class="nv">$source$destination</span><span class="s2">.log"</span></span>
<span id="LC21" class="line">			sort -k 1 -n <span class="s2">"recv_</span><span class="nv">$source$destination</span><span class="s2">.log"</span> &gt; <span class="s2">"trecv_</span><span class="nv">$source$destination</span><span class="s2">.log"</span></span>
<span id="LC22" class="line">			rm -rf <span class="s2">"recv_</span><span class="nv">$source$destination</span><span class="s2">.log"</span></span>
<span id="LC23" class="line">			awk <span class="s1">'{print $2}'</span> <span class="s2">"trecv_</span><span class="nv">$source$destination</span><span class="s2">.log"</span> &gt; <span class="s2">"recv_</span><span class="nv">$source$destination</span><span class="s2">.log"</span></span>
<span id="LC24" class="line">			<span class="c">#rm -rf "recv_$sourcedestination.log"</span></span>
<span id="LC25" class="line">			<span class="c">#cp -rf "trecv_$source$destination.log" "recv_$source$destination.log"</span></span>
<span id="LC26" class="line">			rm -rf <span class="s2">"trecv_</span><span class="nv">$source$destination</span><span class="s2">.log"</span></span>
<span id="LC27" class="line">			<span class="k">if </span>cmp -s <span class="s2">"sent_</span><span class="nv">$source$destination</span><span class="s2">.log"</span> <span class="s2">"recv_</span><span class="nv">$source$destination</span><span class="s2">.log"</span></span>
<span id="LC28" class="line">			<span class="k">then</span></span>
<span id="LC29" class="line"><span class="k">				</span><span class="nb">echo</span> <span class="s2">"Packets from </span><span class="nv">$source</span><span class="s2"> to </span><span class="nv">$destination</span><span class="s2"> are IN-ORDER"</span></span>
<span id="LC30" class="line">				rm -rf <span class="s2">"sent_</span><span class="nv">$source$destination</span><span class="s2">.log"</span> <span class="s2">"recv_</span><span class="nv">$source$destination</span><span class="s2">.log"</span></span>
<span id="LC31" class="line">			<span class="k">else</span></span>
<span id="LC32" class="line"><span class="k">				</span><span class="nb">echo</span> <span class="s2">"ERROR : Packets from </span><span class="nv">$source</span><span class="s2"> to </span><span class="nv">$destination</span><span class="s2"> are NOT IN-ORDER"</span></span>
<span id="LC33" class="line"><span class="c">#				meld "sent_$source$destination.log" "recv_$source$destination.log" </span></span>
<span id="LC34" class="line">			<span class="k">fi</span></span>
<span id="LC35" class="line"><span class="k">		fi</span></span>
<span id="LC36" class="line"><span class="k">	done</span></span>
<span id="LC37" class="line"><span class="k">done</span></span></code></pre>
</div>
</div>


</article>
</div>

</div>
<div class="modal" id="modal-remove-blob">
<div class="modal-dialog">
<div class="modal-content">
<div class="modal-header">
<a class="close" data-dismiss="modal" href="#">×</a>
<h3 class="page-title">Delete inorder_check.sh</h3>
</div>
<div class="modal-body">
<form class="form-horizontal js-replace-blob-form js-quick-submit js-requires-input" action="/watcag/bft-deflection/blob/fpt_2018/src/script/results/inorder_check.sh" accept-charset="UTF-8" method="post"><input name="utf8" type="hidden" value="&#x2713;" /><input type="hidden" name="_method" value="delete" /><input type="hidden" name="authenticity_token" value="fpFcx3ztexgA6zuAS8sBSnDw76ICdA12kQS6BUyVcn3cLsfA8V6PR4NXaEGXqR+cqj8nOYA1twoioXfhtcIf4g==" /><div class="form-group commit_message-group">
<label class="control-label" for="commit_message-d0579eb8638d6933c690bcda24a1c8de">Commit message
</label><div class="col-sm-10">
<div class="commit-message-container">
<div class="max-width-marker"></div>
<textarea name="commit_message" id="commit_message-d0579eb8638d6933c690bcda24a1c8de" class="form-control js-commit-message" placeholder="Delete inorder_check.sh" required="required" rows="3">
Delete inorder_check.sh</textarea>
</div>
</div>
</div>

<div class="form-group branch">
<label class="control-label" for="target_branch">Target branch</label>
<div class="col-sm-10">
<input type="text" name="target_branch" id="target_branch" value="fpt_2018" required="required" class="form-control js-target-branch" />
<div class="js-create-merge-request-container">
<div class="checkbox">
<label for="create_merge_request-5bf8a54f544ddfb8535ddec4cb16a942"><input type="checkbox" name="create_merge_request" id="create_merge_request-5bf8a54f544ddfb8535ddec4cb16a942" value="1" class="js-create-merge-request" checked="checked" />
Start a <strong>new merge request</strong> with these changes
</label></div>
</div>
</div>
</div>
<input type="hidden" name="original_branch" id="original_branch" value="fpt_2018" class="js-original-branch" />

<div class="form-group">
<div class="col-sm-offset-2 col-sm-10">
<button name="button" type="submit" class="btn btn-remove btn-remove-file">Delete file</button>
<a class="btn btn-cancel" data-dismiss="modal" href="#">Cancel</a>
</div>
</div>
</form></div>
</div>
</div>
</div>
<script>
  new NewCommitForm($('.js-replace-blob-form'))
</script>

<div class="modal" id="modal-upload-blob">
<div class="modal-dialog">
<div class="modal-content">
<div class="modal-header">
<a class="close" data-dismiss="modal" href="#">×</a>
<h3 class="page-title">Replace inorder_check.sh</h3>
</div>
<div class="modal-body">
<form class="js-quick-submit js-upload-blob-form form-horizontal" action="/watcag/bft-deflection/update/fpt_2018/src/script/results/inorder_check.sh" accept-charset="UTF-8" method="post"><input name="utf8" type="hidden" value="&#x2713;" /><input type="hidden" name="_method" value="put" /><input type="hidden" name="authenticity_token" value="FC3SnZSdA/0AI61BID14Y1XV3taNX7Hf+35FlKCo18O2kkmaGS73ooOf/oD8X2a1jxoWTQ8eC6NI24hwWf+6XA==" /><div class="dropzone">
<div class="dropzone-previews blob-upload-dropzone-previews">
<p class="dz-message light">
Attach a file by drag &amp; drop or
<a class="markdown-selector" href="#">click to upload</a>
</p>
</div>
</div>
<br>
<div class="alert alert-danger data dropzone-alerts" style="display:none"></div>
<div class="form-group commit_message-group">
<label class="control-label" for="commit_message-91054d52330ddf557f2b45be9c0c5763">Commit message
</label><div class="col-sm-10">
<div class="commit-message-container">
<div class="max-width-marker"></div>
<textarea name="commit_message" id="commit_message-91054d52330ddf557f2b45be9c0c5763" class="form-control js-commit-message" placeholder="Replace inorder_check.sh" required="required" rows="3">
Replace inorder_check.sh</textarea>
</div>
</div>
</div>

<div class="form-group branch">
<label class="control-label" for="target_branch">Target branch</label>
<div class="col-sm-10">
<input type="text" name="target_branch" id="target_branch" value="fpt_2018" required="required" class="form-control js-target-branch" />
<div class="js-create-merge-request-container">
<div class="checkbox">
<label for="create_merge_request-3ca6c913c3d5710e02d069395a8eff8e"><input type="checkbox" name="create_merge_request" id="create_merge_request-3ca6c913c3d5710e02d069395a8eff8e" value="1" class="js-create-merge-request" checked="checked" />
Start a <strong>new merge request</strong> with these changes
</label></div>
</div>
</div>
</div>
<input type="hidden" name="original_branch" id="original_branch" value="fpt_2018" class="js-original-branch" />

<div class="form-actions">
<button name="button" type="submit" class="btn btn-small btn-create btn-upload-file" id="submit-all">Replace file</button>
<a class="btn btn-cancel" data-dismiss="modal" href="#">Cancel</a>
</div>
</form></div>
</div>
</div>
</div>
<script>
  gl.utils.disableButtonIfEmptyField($('.js-upload-blob-form').find('.js-commit-message'), '.btn-upload-file');
  new BlobFileDropzone($('.js-upload-blob-form'), 'put');
  new NewCommitForm($('.js-upload-blob-form'))
</script>

</div>

</div>
</div>
</div>
</div>



</body>
</html>

